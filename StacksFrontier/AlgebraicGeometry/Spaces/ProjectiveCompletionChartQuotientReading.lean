module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentFromBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleHyperplaneReadingChart

/-!
# The reading of the tautological quotient on `U ×_X V`

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module, `P = 𝐏(ℰ ⊕ 𝒪_X)` its
projective completion with affine part `ι : U ⟶ P`, and `V` an étale chart of `X` with a morphism
`m` to the presenting chart. The object `A = U ×_X V` of the site is an étale chart `U_V` of `U`.
This file reads, on the scheme of `A`, the inverse image along `U_V ⟶ U` of
`u^*𝓜 ⟶ ι^*π^*(ℰ ⊕ 𝒪) ⟶ ι^*𝒪_P(1)` for `σ₀ : 𝓜 ⟶ ℰ ⊕ 𝒪`: it is `g^*σ₀_V` followed by the
pulled-back tautological quotient of `𝐏((ℰ ⊕ 𝒪)|_V)` along `A ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`, through the
*canonical* identifications of the sources and an identification of the targets which does not
depend on `σ₀`.

## Main definitions

* `AlgebraicGeometry.Space.affinePartChartOverChart`: the étale chart `U_V` of `U`.

## Main results

* `AlgebraicGeometry.Space.exists_quotientReadingHyp_comp_projectiveBundleTautological`: the
  reading on `A` of `c^*ι^*(π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1)))`, for a morphism `ι : U ⟶ 𝐏(ℰ)` and a
  morphism `c : A ⟶ U` with `A ⟶ P_U ⟶ 𝐏(ℰ)` equal to `c ≫ ι`.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

/-! ### Pulling a base change of tautological quotients back along a further morphism -/

namespace Stacks.RelativeProj

open _root_.AlgebraicGeometry

/-- The abstract shape of the coherence of the comparisons of iterated pullbacks around a base
change square. -/
theorem coherence_shape {C : Type*} [Category C] {o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : C}
    (α : o2 ≅ o1) (P1 : o3 ≅ o9) (P2 : o4 ≅ o10) (Q2 : o7 ≅ o10) (γ3 : o8 ≅ o7) (γ4 : o5 ≅ o8)
    (β : o5 ≅ o4) (X : o2 ⟶ o3) (Bc : o3 ⟶ o4) (R1 : o1 ⟶ o6) (Q1 : o6 ⟶ o9) (Cg : o9 ⟶ o10)
    {R2 : o6 ⟶ o7}
    (a₁ : X ≫ P1.hom = α.hom ≫ R1 ≫ Q1) (a₂ : β.hom ≫ P2.hom = γ4.hom ≫ γ3.hom ≫ Q2.hom)
    (c₁ : P1.inv ≫ Bc ≫ P2.hom = Cg) (e : Q1 ≫ Cg ≫ Q2.inv = R2) :
    α.inv ≫ X ≫ Bc ≫ β.inv = R1 ≫ R2 ≫ γ3.inv ≫ γ4.inv := by
  have hB : Bc = P1.hom ≫ Cg ≫ P2.inv := by
    rw [← c₁]; simp
  have hX : α.inv ≫ X ≫ P1.hom = R1 ≫ Q1 := by
    rw [a₁, Iso.inv_hom_id_assoc]
  have h2 : P2.inv ≫ β.inv = Q2.inv ≫ γ3.inv ≫ γ4.inv := by
    rw [Iso.inv_comp_eq]
    refine Iso.inv_ext ?_
    rw [reassoc_of% a₂]
    simp
  rw [hB, ← e]
  simp only [Category.assoc]
  rw [h2, reassoc_of% hX]

/-- The abstract shape of the pullback along `f` of a base change of quotients. -/
theorem tail_shape {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {d1 d2 d3 d4 d5 d6 : D} {c1 c2 c3 c4 c5 cL cL' : C}
    (t : d1 ⟶ d2) (I1 : d2 ⟶ d2) (A : d2 ⟶ G.obj cL) (A₀ : d1 ⟶ G.obj c1) (bτ : c1 ⟶ cL)
    (tw : cL ⟶ cL') (X1 : c1 ⟶ c2) (B₁ : c2 ⟶ c3) (Y1 : c3 ⟶ c4) (Θ : c4 ⟶ c5) (τ' : c5 ⟶ cL')
    (R1 : d1 ⟶ d3) (R2 : d3 ⟶ d4) (R3 : d4 ⟶ d5) (Θg : d5 ⟶ d6) (I2 : d6 ⟶ d6)
    (R4' : d6 ⟶ G.obj c5) (R4 : d5 ⟶ G.obj c4)
    (h₁ : I1 = 𝟙 _) (h₂ : I2 = 𝟙 _) (n₁ : t ≫ A = A₀ ≫ G.map bτ)
    (hsp : bτ ≫ tw = X1 ≫ B₁ ≫ Y1 ≫ Θ ≫ τ') (n₂ : Θg ≫ R4' = R4 ≫ G.map Θ)
    (core : A₀ ≫ G.map X1 ≫ G.map B₁ ≫ G.map Y1 = R1 ≫ R2 ≫ R3 ≫ R4) :
    t ≫ I1 ≫ A ≫ G.map tw = R1 ≫ R2 ≫ R3 ≫ Θg ≫ I2 ≫ R4' ≫ G.map τ' := by
  subst h₁ h₂
  simp only [Category.id_comp]
  rw [reassoc_of% n₁, ← G.map_comp, hsp, reassoc_of% n₂]
  simp only [G.map_comp]
  rw [reassoc_of% core]

/-- Transports along three equalities of morphisms compose. -/
theorem pullbackCongr_hom_app_trans_trans_inv {T Y : Scheme.{u}} {p q r w : T ⟶ Y} (h₁ : p = q)
    (h₂ : q = r) (h₃ : w = r) (h : p = w) (F : Y.Modules) :
    (Scheme.Modules.pullbackCongr h₁).hom.app F ≫ (Scheme.Modules.pullbackCongr h₂).hom.app F ≫
      (Scheme.Modules.pullbackCongr h₃).inv.app F = (Scheme.Modules.pullbackCongr h).hom.app F := by
  subst h₁ h₂ h₃
  simp [Scheme.Modules.pullbackCongr]

/-- **The base change of a tautological quotient, pulled back along `f`.** Let `b : P' ⟶ P` lie
over `ms : Y' ⟶ Y` and carry `τ : ρ^*F ⟶ L` to `τ' : ρ'^*F' ⟶ L'` along `F' ≅ ms^*F` and
`b^*L ≅ L'` (`hspec`, the shape of Stacks 01O3). For `f : T ⟶ P'`, the pullback of `τ` along
`kk = f ≫ b` is the pullback of `τ'` along `f`, through the comparisons of iterated pullbacks
along `kk ≫ ρ = gg ≫ ms` with `gg = f ≫ ρ'`. -/
theorem pullback_map_comp_eq_of_baseChange_of_comp {T P' P Y' Y : Scheme.{u}} (f : T ⟶ P')
    (b : P' ⟶ P) {ρ : P ⟶ Y} {ρ' : P' ⟶ Y'} {ms : Y' ⟶ Y} (hw : b ≫ ρ = ρ' ≫ ms)
    {F : Y.Modules} {F' : Y'.Modules} (θF : F' ≅ (Scheme.Modules.pullback ms).obj F)
    {L : P.Modules} {L' : P'.Modules} (τ : (Scheme.Modules.pullback ρ).obj F ⟶ L)
    (τ' : (Scheme.Modules.pullback ρ').obj F' ⟶ L') (tw : (Scheme.Modules.pullback b).obj L ≅ L')
    (hspec : (Scheme.Modules.pullback b).map τ ≫ tw.hom =
      (Scheme.Modules.pullbackComp b ρ).hom.app F ≫ (Scheme.Modules.pullbackCongr hw).hom.app F ≫
        (Scheme.Modules.pullbackComp ρ' ms).inv.app F ≫ (Scheme.Modules.pullback ρ').map θF.inv ≫
          τ')
    (kk : T ⟶ P) (hkk : f ≫ b = kk) (gg : T ⟶ Y') (hg : f ≫ ρ' = gg) (hk : kk ≫ ρ = gg ≫ ms) :
    (Scheme.Modules.pullback kk).map τ ≫ ((Scheme.Modules.pullbackCongr hkk).inv.app L ≫
        (Scheme.Modules.pullbackComp f b).inv.app L ≫ (Scheme.Modules.pullback f).map tw.hom) =
      (Scheme.Modules.pullbackComp kk ρ).hom.app F ≫ (Scheme.Modules.pullbackCongr hk).hom.app F ≫
        (Scheme.Modules.pullbackComp gg ms).inv.app F ≫ (Scheme.Modules.pullback gg).map θF.inv ≫
        ((Scheme.Modules.pullbackCongr hg).inv.app F' ≫
          (Scheme.Modules.pullbackComp f ρ').inv.app F' ≫ (Scheme.Modules.pullback f).map τ') := by
  subst hkk hg
  have core : (Scheme.Modules.pullbackComp f b).inv.app ((Scheme.Modules.pullback ρ).obj F) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp b ρ).hom.app F) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr hw).hom.app F) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp ρ' ms).inv.app F) =
      (Scheme.Modules.pullbackComp (f ≫ b) ρ).hom.app F ≫
        (Scheme.Modules.pullbackCongr hk).hom.app F ≫
        (Scheme.Modules.pullbackComp (f ≫ ρ') ms).inv.app F ≫
        (Scheme.Modules.pullbackComp f ρ').inv.app ((Scheme.Modules.pullback ms).obj F) :=
    coherence_shape ((Scheme.Modules.pullbackComp f b).app ((Scheme.Modules.pullback ρ).obj F))
      ((Scheme.Modules.pullbackComp f (b ≫ ρ)).app F)
      ((Scheme.Modules.pullbackComp f (ρ' ≫ ms)).app F)
      ((Scheme.Modules.pullbackCongr (Category.assoc f ρ' ms)).app F)
      ((Scheme.Modules.pullbackComp (f ≫ ρ') ms).app F)
      ((Scheme.Modules.pullbackComp f ρ').app ((Scheme.Modules.pullback ms).obj F))
      ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp ρ' ms).app F))
      _ _ _ _ _
      (Stacks.Groupoids.map_pullbackComp_hom_app_comp f b ρ F)
      (Stacks.Groupoids.map_pullbackComp_hom_app_comp f ρ' ms F)
      (Stacks.Groupoids.pullbackComp_congr_app f hw F)
      (pullbackCongr_hom_app_trans_trans_inv (Category.assoc f b ρ)
        (by rw [hw] : f ≫ b ≫ ρ = f ≫ ρ' ≫ ms) (Category.assoc f ρ' ms) hk F)
  exact tail_shape (Scheme.Modules.pullback f) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    ((Scheme.Modules.pullbackComp f b).inv.naturality τ) hspec
    ((Scheme.Modules.pullbackComp f ρ').inv.naturality θF.inv) core

end Stacks.RelativeProj

namespace AlgebraicGeometry.Space

/-- The abstract shape of the coherence of the comparisons of iterated inverse images along two
factorizations `c' ≫ ι = rk ≫ at` of a morphism to `P`, followed by `π`. -/
theorem _root_.CategoryTheory.two_factorization_coherence_shape {C C₁ C₂ : Type*} [Category C]
    [Category C₁] [Category C₂] (G₁ : C₁ ⥤ C) (G₂ : C₂ ⥤ C) {c d : C} {x₁ y₁ : C₁}
    {x₂ y₂ : C₂} (P1 : x₁ ≅ y₁) (P2 : d ≅ G₁.obj y₁) (T1 : c ≅ G₁.obj x₁)
    (Qi : c ≅ d) (T2 : c ≅ G₂.obj x₂) (P4 : x₂ ≅ y₂) (P3 : d ≅ G₂.obj y₂)
    (h₁ : T1 ≪≫ G₁.mapIso P1 = Qi ≪≫ P2) (h₂ : T2 ≪≫ G₂.mapIso P4 = Qi ≪≫ P3) :
    G₁.map P1.hom ≫ P2.inv ≫ P3.hom = T1.inv ≫ T2.hom ≫ G₂.map P4.hom := by
  have k₁ := congrArg Iso.hom h₁
  have k₂ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Functor.mapIso_hom] at k₁ k₂
  have hC : G₁.map P1.hom = T1.inv ≫ Qi.hom ≫ P2.hom := by
    rw [Iso.eq_inv_comp]; exact k₁
  rw [hC]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [k₂]

/-- The abstract shape of the factorization of `c^*ι^*(π^*σ₀ ≫ τ)` through the inverse image of
the chart quotient along `rk`. -/
theorem _root_.CategoryTheory.chart_quotient_factor_shape {C C' : Type*} [Category C]
    [Category C'] (G : C' ⥤ C) {n₁ n₂ n₃ o₁ o₂ n₆ n₇ : C} {a b t' o' e8 e8' : C'}
    (q' : n₁ ⟶ o₁) (Cm : n₁ ⟶ n₂) (L1 : n₂ ⟶ o₁) (hq' : q' = Cm ≫ L1)
    (P2 : n₃ ≅ n₂) (Xφ : n₃ ⟶ o₂) (P2' : o₂ ≅ o₁) (hL1 : L1 = P2.inv ≫ Xφ ≫ P2'.hom)
    (P3 : n₃ ≅ G.obj a) (P3' : o₂ ≅ G.obj o') (Rφ' : a ⟶ o')
    (hX : G.map Rφ' = P3.inv ≫ Xφ ≫ P3'.hom)
    (Ys' : a ⟶ b) (Qc : b ⟶ t') (twAt : o' ≅ t') (hA : Rφ' = Ys' ≫ Qc ≫ twAt.inv)
    (κ' : n₁ ⟶ n₆) (Sσ : n₆ ⟶ n₇) (K1 : n₇ ⟶ G.obj e8) (K1M : n₆ ⟶ G.obj e8')
    (σ8 : e8' ⟶ e8) (N1 : Sσ ≫ K1 = K1M ≫ G.map σ8)
    (pE : e8 ⟶ b) (pM : e8' ⟶ a) (N2 : σ8 ≫ pE = pM ≫ Ys')
    (κ₀inv : n₇ ⟶ G.obj b) (hκ : κ₀inv = K1 ≫ G.map pE)
    (τhom : G.obj t' ⟶ o₁) (hτ : τhom = G.map twAt.inv ≫ P3'.inv ≫ P2'.hom)
    (coh : Cm ≫ P2.inv ≫ P3.hom = κ' ≫ K1M ≫ G.map pM) :
    q' = κ' ≫ Sσ ≫ κ₀inv ≫ G.map Qc ≫ τhom := by
  have hXφ : Xφ = P3.hom ≫ G.map Ys' ≫ G.map Qc ≫ G.map twAt.inv ≫ P3'.inv := by
    have h0 : Xφ = P3.hom ≫ G.map Rφ' ≫ P3'.inv := by rw [hX]; simp
    rw [h0, hA]; simp only [G.map_comp, Category.assoc]
  rw [hq', hL1, hXφ, hκ, hτ]
  simp only [Category.assoc]
  rw [reassoc_of% N1, ← G.map_comp_assoc σ8 pE, N2, G.map_comp_assoc]
  simp only [← Category.assoc] at coh ⊢
  rw [coh]

/-! ### Two factorizations of a morphism to `P`, at the level of modules -/

section Factor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`c^*ι^*(π^*σ₀ ≫ τ)` through the inverse image along `rk` of a factorization of `at^*τ`**,
for two factorizations `rk ≫ at = c ≫ ι` of a morphism to `P`. -/
theorem modulePullback_map_comp_eq_of_two_factorizations {A' U P Pu X : AlgebraicSpaces B S hS}
    (c : A' ⟶ U) (ι : U ⟶ P) (π : P ⟶ X) (rk : A' ⟶ Pu) (at' : Pu ⟶ P) (H : rk ≫ at' = c ≫ ι)
    (wk : rk ≫ (at' ≫ π) = c ≫ (ι ≫ π)) {E M : Modules.{u, u} B S hS X.1 X.2} (σ₀ : M ⟶ E)
    {O : Modules.{u, u} B S hS P.1 P.2} (τ : (modulePullback B S hS π).obj E ⟶ O)
    {Lc : Modules.{u, u} B S hS Pu.1 Pu.2}
    (cq : (modulePullback B S hS at').obj ((modulePullback B S hS π).obj E) ⟶ Lc)
    (tw : (modulePullback B S hS at').obj O ≅ Lc)
    (hc : (modulePullback B S hS at').map τ ≫ tw.hom = cq) :
    (modulePullback B S hS c).map
        ((QuasiCoherentDescent.pullbackComparison B S hS ι π (ι ≫ π) rfl M).hom ≫
          (modulePullback B S hS ι).map ((modulePullback B S hS π).map σ₀ ≫ τ)) =
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl M).symm.hom ≫
        (modulePullback B S hS (c ≫ (ι ≫ π))).map σ₀ ≫
        ((modulePullback B S hS rk).mapIso
            (QuasiCoherentDescent.pullbackComparison B S hS at' π _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS rk (at' ≫ π) _ wk E).symm).inv ≫
        (modulePullback B S hS rk).map cq ≫
        ((modulePullback B S hS rk).mapIso tw.symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS rk at' (c ≫ ι) H O).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS c ι (c ≫ ι) rfl O).hom := by
  have hc' : (modulePullback B S hS at').map τ = cq ≫ tw.inv := by
    rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hst : (c ≫ ι) ≫ π = c ≫ (ι ≫ π) := Category.assoc _ _ _
  refine chart_quotient_factor_shape (modulePullback B S hS rk) _ _ _ (Functor.map_comp _ _ _)
    _ _ _ (modulePullback_map_modulePullback_map_eq c ι (c ≫ ι) rfl _) _ _ _
    (modulePullback_map_modulePullback_map_eq rk at' (c ≫ ι) H _) _ _ _
    (((modulePullback B S hS at').map_comp _ _).trans (congrArg (_ ≫ ·) hc')) _ _ _ _ _
    (QuasiCoherentDescent.pullbackComparison_naturality B S hS rk (at' ≫ π) _ wk σ₀) _ _
    (QuasiCoherentDescent.pullbackComparison_naturality B S hS at' π _ rfl σ₀) _
    (by simp) _ (by simp) ?_
  exact two_factorization_coherence_shape (modulePullback B S hS c) (modulePullback B S hS rk)
    _ _ _ (QuasiCoherentDescent.pullbackComparison B S hS (c ≫ ι) π _ hst M) _ _ _
    (QuasiCoherentDescent.pullbackComparison_trans B S hS c ι π _ rfl (c ≫ ι) rfl _ rfl hst M)
    (QuasiCoherentDescent.pullbackComparison_trans B S hS rk at' π _ rfl (c ≫ ι) H _ wk hst M)

/-- `AlgebraicGeometry.Space.modulePullback_map_comp_eq_of_two_factorizations`, with the
identifications given as variables. -/
theorem modulePullback_map_comp_eq_of_two_factorizations' {A' U P Pu X : AlgebraicSpaces B S hS}
    (c : A' ⟶ U) (ι : U ⟶ P) (π : P ⟶ X) (rk : A' ⟶ Pu) (at' : Pu ⟶ P) (H : rk ≫ at' = c ≫ ι)
    (wk : rk ≫ (at' ≫ π) = c ≫ (ι ≫ π)) {E M : Modules.{u, u} B S hS X.1 X.2} (σ₀ : M ⟶ E)
    {O : Modules.{u, u} B S hS P.1 P.2} (τ : (modulePullback B S hS π).obj E ⟶ O)
    {Lc : Modules.{u, u} B S hS Pu.1 Pu.2}
    (cq : (modulePullback B S hS at').obj ((modulePullback B S hS π).obj E) ⟶ Lc)
    (tw : (modulePullback B S hS at').obj O ≅ Lc)
    (hc : (modulePullback B S hS at').map τ ≫ tw.hom = cq)
    (κ₀ : (modulePullback B S hS rk).obj ((modulePullback B S hS at').obj
      ((modulePullback B S hS π).obj E)) ≅ (modulePullback B S hS (c ≫ (ι ≫ π))).obj E)
    (hκ₀ : κ₀ = (modulePullback B S hS rk).mapIso
            (QuasiCoherentDescent.pullbackComparison B S hS at' π _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS rk (at' ≫ π) _ wk E).symm)
    (θ : (modulePullback B S hS rk).obj Lc ≅
      (modulePullback B S hS c).obj ((modulePullback B S hS ι).obj O))
    (hθ : θ = (modulePullback B S hS rk).mapIso tw.symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS rk at' (c ≫ ι) H O).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS c ι (c ≫ ι) rfl O) :
    (modulePullback B S hS c).map
        ((QuasiCoherentDescent.pullbackComparison B S hS ι π (ι ≫ π) rfl M).hom ≫
          (modulePullback B S hS ι).map ((modulePullback B S hS π).map σ₀ ≫ τ)) =
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl M).symm.hom ≫
        (modulePullback B S hS (c ≫ (ι ≫ π))).map σ₀ ≫ κ₀.inv ≫
        (modulePullback B S hS rk).map cq ≫ θ.hom := by
  subst hκ₀ hθ
  exact modulePullback_map_comp_eq_of_two_factorizations c ι π rk at' H wk σ₀ τ cq tw hc

end Factor

/-! ### Precomposing a read quotient -/

section Precomp

/-- The abstract shape of the reading of a quotient precomposed with the inverse image of a
morphism of modules. -/
theorem _root_.CategoryTheory.precomp_reading_shape {C₀ : Type*} [Category C₀]
    {a a' b b' k k' ρE ρM t₀ : C₀} (Zq' : a' ⟶ b') (K' : a' ≅ k') (Zs : k' ⟶ k) (K : a ≅ k)
    (Zq : a ⟶ b) (Zτ : b ≅ b') (SF : ρE ≅ k) (SM : ρM ≅ k') (Rs : ρM ⟶ ρE) (univ : ρE ⟶ t₀)
    (ε : b ≅ t₀) (hZ : Zq' = K'.hom ≫ Zs ≫ K.inv ≫ Zq ≫ Zτ.hom)
    (hq : Zq = K.hom ≫ SF.inv ≫ univ ≫ ε.inv) (hnat : Rs ≫ SF.hom = SM.hom ≫ Zs) :
    Zq' = K'.hom ≫ SM.inv ≫ (Rs ≫ univ) ≫ (Zτ.symm ≪≫ ε).inv := by
  have hnat' : Zs ≫ SF.inv = SM.inv ≫ Rs := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hZ, hq]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hnat']

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **A read quotient precomposed with the inverse image of `σ₀ : 𝓜 ⟶ ℰ` is read as
`ρ^*σ₀_Y` followed by the reading.** -/
theorem quotientReadingHyp_precomp (E : Modules.{u, u} B S hS X.1 X.2)
    (hE : E.IsQuasicoherentOnSite) {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψU : representedAlgebraicSpace B S hS T ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    {N L N' L' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E) (hq : QuotientReadingHyp E hE wρ univ εL q κ₀)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ E)
    (q' : N' ⟶ L') (κ' : N' ≅ (modulePullback B S hS ψU).obj M) (τ : L ≅ L')
    (h' : q' = κ'.hom ≫ (modulePullback B S hS ψU).map σ₀ ≫ κ₀.inv ≫ q ≫ τ.hom) :
    QuotientReadingHyp M hM wρ
      ((Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).map
          (schemeReadingMap ψY σ₀) ≫ univ)
      (((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso τ)).symm ≪≫ εL)
      q' κ' := by
  unfold QuotientReadingHyp quotientReadingOf at hq ⊢
  subst h'
  refine precomp_reading_shape _ _
    (schemeReadingMap ψU σ₀) _ _ _ (schemeReadingPullbackIso E hE ρ wρ)
    (schemeReadingPullbackIso M hM ρ wρ) _ univ εL ?_ hq
    (schemeReadingPullbackIso_hom_naturality ρ wρ hM hE σ₀)
  simp only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv]

end Precomp

/-! ### The reading on an object over a chart bundle, for a general module -/

section General

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) {A : BigFppfOver B S hS}
  (h : A ⟶ (projectiveBundleChartFamily E hfree).site V)
  {ψR : representedAlgebraicSpace B S hS A ⟶ X}
  (wk : representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h) ≫
    (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) = ψR)
  (wρ : representedSpaceMap B S hS (h ≫ (projectiveBundleChartFamily E hfree).siteToChart V) ≫
    chartToSpace B S hS X V = ψR)

/-- The morphism `A ⟶ P_V ⟶ P_U` followed by the projection `P_U ⟶ U` equals the composite
`A ⟶ 𝐏(ℰ|_V) ⟶ V ⟶ U`. -/
theorem chartBundleHomOfSiteToPresenting_comp_chartProj :
    chartBundleHomOfSiteToPresenting E hfree m h ≫ projectiveBundleChartProj E hfree =
      (h ≫ (projectiveBundleChartFamily E hfree).siteToChart V) ≫
        (SmallEtale.toOver B S hS X.1).map m := by
  rw [Category.assoc, Category.assoc, siteMap_comp_siteToChart E hfree m]

/-- The morphism `A ⟶ 𝐏(ℰ|_V)` followed by the structure morphism `𝐏(ℰ|_V) ⟶ V` is the
morphism of schemes underlying `A ⟶ V`. -/
theorem chartBundleHomOfSite_comp_chartBundleToChart :
    chartBundleHomOfSite E hfree h ≫ chartBundleToChart E V =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (h ≫ (projectiveBundleChartFamily E hfree).siteToChart V).left :=
  rfl

include wk wρ in
/-- **The tautological quotient of the presenting chart bundle, pulled back along `A ⟶ P_V ⟶ P_U`,
reads as the tautological quotient of `𝐏(ℰ|_V)` pulled back along `A ⟶ 𝐏(ℰ|_V)`**, through the
canonical identification of the sources (Stacks 01O3 along `m`). -/
theorem exists_quotientReadingHyp_chartBundleHomOfSiteToPresenting :
    ∃ ε, QuotientReadingHyp E hE wρ
      ((Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
        (chartBundleHomOfSite E hfree h) (chartBundleHomOfSite_comp_chartBundleToChart E hfree h)) ε
      ((modulePullback B S hS (representedSpaceMap B S hS
        (chartBundleHomOfSiteToPresenting E hfree m h))).map
        (projectiveBundleChartQuotient E hfree))
      ((modulePullback B S hS (representedSpaceMap B S hS
          (chartBundleHomOfSiteToPresenting E hfree m h))).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h))
          (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) ψR wk E).symm) :=
  ⟨_, quotientReadingHyp_modulePullback E hE (chartBundleHomOfSiteToPresenting E hfree m h)
    (chartBundleHomOfSiteToPresenting_comp_chartProj E hfree m h)
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree) wk
    (representedSpaceMap_toOver_map_comp_chartToSpace m) wρ
    (chartBundleTautological E (bundleBaseChart X))
    ((Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
        (chartBundleHomOfSite E hfree h) (chartBundleHomOfSite_comp_chartBundleToChart E hfree h))
    ((Scheme.Modules.pullbackCongr
        (schemeHom_chartBundleHomOfSiteToPresenting E hfree m h).symm).symm.app _ ≪≫
      (Scheme.Modules.pullbackComp (chartBundleHomOfSite E hfree h) (chartBundleMap E m)).symm.app
        _ ≪≫
      (Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).mapIso (chartBundleTwistIso E m))
    (Stacks.RelativeProj.pullback_map_comp_eq_of_baseChange_of_comp
      (chartBundleHomOfSite E hfree h) (chartBundleMap E m)
      (Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase
        (chartSchemeMapOfSite m) (chartBundleModule E (bundleBaseChart X)) (chartBundleModule E V)
        (chartBundleModuleIso E m))
      (chartBundleModuleIso E m) (chartBundleTautological E (bundleBaseChart X))
      (chartBundleTautological E V) (chartBundleTwistIso E m) (chartBundleTwistIso_spec E m) _
      (schemeHom_chartBundleHomOfSiteToPresenting E hfree m h).symm _
      (chartBundleHomOfSite_comp_chartBundleToChart E hfree h)
      (schemeHom_comp_eq_of_eq (chartBundleHomOfSiteToPresenting_comp_chartProj E hfree m h)))
    (isQuasicoherentOnSite_projectiveBundleChartModule E hfree)
    (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree)
    (projectiveBundleChartTwistReadingIso E hfree) (projectiveBundleChartQuotient E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm
    (quotientReadingHyp_projectiveBundle E hfree)⟩

include wk wρ in
/-- `AlgebraicGeometry.Space.exists_quotientReadingHyp_chartBundleHomOfSiteToPresenting`, with
the identification of the sources given as a variable. -/
theorem exists_quotientReadingHyp_chartBundleHomOfSiteToPresenting_of_eq
    (κ : (modulePullback B S hS (representedSpaceMap B S hS
        (chartBundleHomOfSiteToPresenting E hfree m h))).obj (projectiveBundleChartModule E hfree) ≅
      (modulePullback B S hS ψR).obj E)
    (hκ : κ = (modulePullback B S hS (representedSpaceMap B S hS
          (chartBundleHomOfSiteToPresenting E hfree m h))).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h))
          (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) ψR wk E).symm) :
    ∃ ε, QuotientReadingHyp E hE wρ
      ((Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
        (chartBundleHomOfSite E hfree h) (chartBundleHomOfSite_comp_chartBundleToChart E hfree h)) ε
      ((modulePullback B S hS (representedSpaceMap B S hS
        (chartBundleHomOfSiteToPresenting E hfree m h))).map
        (projectiveBundleChartQuotient E hfree))
      κ := by
  subst hκ
  exact exists_quotientReadingHyp_chartBundleHomOfSiteToPresenting E hfree m h wk wρ

end General

section Tautological

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
  AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) {A : BigFppfOver B S hS}
  (h : A ⟶ (projectiveBundleChartFamily E hfree).site V)
  {U : AlgebraicSpaces B S hS} (ι : U ⟶ projectiveBundle E hfree)
  (c : representedAlgebraicSpace B S hS A ⟶ U)
  (H : representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h) ≫
    projectiveBundleAtlas E hfree = c ≫ ι)

include H in
/-- If `A ⟶ P_U ⟶ P` equals `c ≫ ι`, then its composite with the projection `P ⟶ X` is
`c ≫ ι ≫ (P ⟶ X)`. -/
theorem representedSpaceMap_chartBundleHomOfSiteToPresenting_comp_proj :
    representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h) ≫
      (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) =
    c ≫ (ι ≫ projectiveBundleProj E hfree) :=
  by rw [← Category.assoc, H, Category.assoc]

include H in
/-- **The reading on `A` of `c^*ι^*(π^*σ₀ ≫ (π^*ℰ ⟶ 𝒪(1)))`** for a morphism `ι : U ⟶ P` and a
morphism `c : A ⟶ U` with `A ⟶ P_U ⟶ P` equal to `c ≫ ι`: it is `g^*σ₀_V` followed by the
pulled-back tautological quotient of `𝐏(ℰ|_V)` along `A ⟶ 𝐏(ℰ|_V)`, through the canonical
identifications of the sources and an identification of the targets independent of `σ₀`. -/
theorem exists_quotientReadingHyp_comp_projectiveBundleTautological
    (wρ : representedSpaceMap B S hS (h ≫ (projectiveBundleChartFamily E hfree).siteToChart V) ≫
      chartToSpace B S hS X V = c ≫ (ι ≫ projectiveBundleProj E hfree)) :
    ∃ ε : representedZariskiModule B S hS A ((modulePullback B S hS c).obj
          ((modulePullback B S hS ι).obj (projectiveBundleTwist E hfree).obj)) ≅
        (Scheme.Modules.pullback (chartBundleHomOfSite E hfree h)).obj (chartBundleTwist E V),
      ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ E),
        QuotientReadingHyp M hM wρ
          ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B)
              (h ≫ (projectiveBundleChartFamily E hfree).siteToChart V).left)).map
            (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫
            (Stacks.RelativeProj.tautologicalDatum (chartBundleModule E V)).overQuotientMap
              (chartBundleHomOfSite E hfree h)
              (chartBundleHomOfSite_comp_chartBundleToChart E hfree h)) ε
          ((modulePullback B S hS c).map
            ((QuasiCoherentDescent.pullbackComparison B S hS ι (projectiveBundleProj E hfree)
                (ι ≫ projectiveBundleProj E hfree) rfl M).hom ≫
              (modulePullback B S hS ι).map ((modulePullback B S hS
                (projectiveBundleProj E hfree)).map σ₀ ≫
                (projectiveBundleTautological E hfree).hom)))
          (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ projectiveBundleProj E hfree)
            (c ≫ (ι ≫ projectiveBundleProj E hfree)) rfl M).symm := by
  have wk := representedSpaceMap_chartBundleHomOfSiteToPresenting_comp_proj E hfree m h ι c H
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : (modulePullback B S hS (representedSpaceMap B S hS
        (chartBundleHomOfSiteToPresenting E hfree m h))).obj (projectiveBundleChartModule E hfree) ≅
      (modulePullback B S hS (c ≫ (ι ≫ projectiveBundleProj E hfree))).obj E,
      κ₀ = (modulePullback B S hS (representedSpaceMap B S hS
          (chartBundleHomOfSiteToPresenting E hfree m h))).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h))
          (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) _ wk E).symm := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : (modulePullback B S hS (representedSpaceMap B S hS
        (chartBundleHomOfSiteToPresenting E hfree m h))).obj (projectiveBundleChartTwist E hfree) ≅
      (modulePullback B S hS c).obj ((modulePullback B S hS ι).obj
        (projectiveBundleTwist E hfree).obj),
      θ = (modulePullback B S hS (representedSpaceMap B S hS
          (chartBundleHomOfSiteToPresenting E hfree m h))).mapIso
          (projectiveBundleTwistAtlasIso E hfree).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS
          (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h))
          (projectiveBundleAtlas E hfree) (c ≫ ι) H (projectiveBundleTwist E hfree).obj).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS c ι (c ≫ ι) rfl
          (projectiveBundleTwist E hfree).obj := ⟨_, rfl⟩
  obtain ⟨ε₁, h₁⟩ := exists_quotientReadingHyp_chartBundleHomOfSiteToPresenting_of_eq E hfree m h
    wk wρ κ₀ hκ₀
  have hc0 : (modulePullback B S hS (projectiveBundleAtlas E hfree)).map
      (X := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
      (projectiveBundleTautological E hfree).hom ≫ (projectiveBundleTwistAtlasIso E hfree).hom =
        projectiveBundleChartQuotient E hfree :=
    modulePullback_map_projectiveBundleTautological E hfree
  refine ⟨_, fun M hM σ₀ => quotientReadingHyp_precomp E hE wρ _ ε₁ _ κ₀ h₁ M hM σ₀ _ _ θ ?_⟩
  have key := modulePullback_map_comp_eq_of_two_factorizations'
    (A' := representedAlgebraicSpace B S hS A) (Pu := (projectiveBundleGroupoid E hfree).objects)
    c ι (projectiveBundleProj E hfree)
    (representedSpaceMap B S hS (chartBundleHomOfSiteToPresenting E hfree m h))
    (projectiveBundleAtlas E hfree) H wk σ₀ (projectiveBundleTautological E hfree).hom
    (projectiveBundleChartQuotient E hfree) (projectiveBundleTwistAtlasIso E hfree)
    hc0 κ₀ (hκ₀.trans (by with_reducible rfl)) θ (hθ.trans (by with_reducible rfl))
  with_reducible exact key

end Tautological


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X)

omit [SheafOfModules.IsFiniteLocallyFree (have this := E; this)] in
/-- The morphism `U ×_X V ⟶ U` is étale: it is the base change of the chart `V ⟶ X`. -/
theorem isEtale_projectiveCompletionAffinePartOverChartToAffinePart :
    IsEtale B S hS (projectiveCompletionAffinePartOverChartToAffinePart E hr m) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (isEtale_iff_presheaf_of_yoneda B S hS _).2
    (MorphismProperty.of_isPullback (isPullback_projectiveCompletionAffinePart_toChart E hr m).flip
      V.2)

/-- **The étale chart `U_V = U ×_X V` of the affine part `U`.** -/
abbrev affinePartChartOverChart : SmallEtale B S hS (projectiveCompletionAffinePart E hr).1 :=
  etaleChartOfIsEtale B S hS (projectiveCompletionAffinePartOverChartToAffinePart E hr m)
    (isEtale_projectiveCompletionAffinePartOverChartToAffinePart E hr m)

example : (SmallEtale.toOver B S hS _).obj (affinePartChartOverChart E hr m) =
    projectiveCompletionAffinePartOverChart E hr m := rfl

omit [SheafOfModules.IsFiniteLocallyFree (have this := E; this)] in
/-- The chart `U_V ⟶ U` followed by `u : U ⟶ X` is `U_V ⟶ V ⟶ X`. -/
theorem representedSpaceMap_affinePartOverChartToChart_comp :
    representedSpaceMap B S hS (projectiveCompletionAffinePartOverChartToChart E hr m) ≫
        chartToSpace B S hS X V =
      chartToSpace B S hS _ (affinePartChartOverChart E hr m) ≫
        projectiveCompletionAffinePartProj E hr :=
  ObjectProperty.hom_ext _ (isPullback_projectiveCompletionAffinePart_toChart E hr m).w.symm

attribute [local implicit_reducible] AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
  AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

/-- The morphism `A = U ×_X V ⟶ P_V ⟶ P_U` of the site to the presenting chart bundle. -/
abbrev affinePartOverChartToPresenting :
    projectiveCompletionAffinePartOverChart E hr m ⟶
      (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
        (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)).U :=
  @splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m ≫
    (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).siteMap m

omit [SheafOfModules.IsFiniteLocallyFree (have this := E; this)] in
/-- The morphism `A ⟶ P_V ⟶ P_U` followed by the projection `P_U ⟶ U` equals `A ⟶ V ⟶ U`. -/
theorem affinePartOverChartToPresenting_comp_chartProj :
    affinePartOverChartToPresenting E hr m ≫
        @projectiveBundleChartProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr) =
      projectiveCompletionAffinePartOverChartToChart E hr m ≫
        (SmallEtale.toOver B S hS X.1).map m := by
  rw [Category.assoc, @siteMap_comp_siteToChart B S hS X (addUnit X.2 E)
    (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr) _ _ m]
  rfl

omit [SheafOfModules.IsFiniteLocallyFree (have this := E; this)] in
/-- The chart `U_V ⟶ U ⟶ P` is `A ⟶ P_U ⟶ P`. -/
theorem representedSpaceMap_affinePartOverChartToPresenting_comp :
    representedSpaceMap B S hS (affinePartOverChartToPresenting E hr m) ≫
        (@projectiveBundleAtlas B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr) ≫
        @projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr)) =
      chartToSpace B S hS _ (affinePartChartOverChart E hr m) ≫
        projectiveCompletionAffinePartProj E hr := by
  have h := (@isPullback_splitEpiComplementChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m).w
  have H : representedSpaceMap B S hS (affinePartOverChartToPresenting E hr m) ≫
      @projectiveBundleAtlas B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr) =
      chartToSpace B S hS _ (affinePartChartOverChart E hr m) ≫
        projectiveCompletionAffinePartHom E hr := by
    refine ObjectProperty.hom_ext _ ?_
    refine Eq.trans ?_ h.symm
    exact (congrArg (· ≫ _) (yoneda.map_comp _ _)).trans (Category.assoc _ _ _)
  rw [← Category.assoc, H]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Space

end
