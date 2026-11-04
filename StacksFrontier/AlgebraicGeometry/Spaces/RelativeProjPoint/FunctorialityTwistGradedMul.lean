module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGlued
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGradedMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackChartMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraUnit

/-!
# Multiplicativity of the glued maps `θ_d` of Stacks 085F, over a presentation

For a map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`, with
`P = Proj_X(𝒜)`, `Q = Proj_X(ℬ)`, the open `U(ψ) ⊆ Q` and `r_ψ : U(ψ) ⟶ P`, the maps
`θ_d : r_ψ^*𝒪_P(d) ⟶ 𝒪_Q(d)|_{U(ψ)}` are glued from the maps `θ_d` of Tag 07ZG on the atlas
`U(ψ) ×_X U` of `U(ψ)`. Such glued maps carry the multiplications of the descended modules,
pulled back along `r_ψ` and `ι : U(ψ) ⟶ Q` and read through Stacks 03EL, to one another as soon
as their chart maps carry the pulled-back chart multiplications to one another. The chart maps
`θ_d` of Tag 07ZG carry the pulled-back multiplication of the twists of `P ×_X U` to that of
`Q ×_X U`.

## Main results

* `AlgebraicGeometry.Space.mul_comp_eq_of_two_chart_readings`: multiplicativity read through a
  faithful functor and chart identifications.
* `AlgebraicGeometry.Space.modulePullback_map_pullbackTensorIso_inv_comp_reading`: the inverse
  image along a chart of a pulled-back multiplication, read along a square.
* `AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso_mul_reading`: the same through
  the chart identifications `AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`.
* `AlgebraicGeometry.Space.mul_comp_of_isAtlasMapComp` and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.mul_comp_of_isChartHom`: morphisms
  `r^*𝒟₁ ⟶ ι^*𝒟₂` which are chart maps carry multiplications to multiplications.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartTwistMapRefl_mul` and
  `AlgebraicGeometry.Space.RelativeProjSituation.twistChartMap_mul`: the chart maps `θ_d` of
  Tag 07ZG are multiplicative.
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry


/-! ### The map `θ` of Tag 07ZG on a chart carries the pulled-back multiplication -/

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)

variable {S₀ : Scheme.{u}} {A B : SheafGradedAlgebra S₀} (ψ : SheafGradedAlgebraHom A B)
  {C P Q : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q) (p : P ⟶ (relativeProj A).scheme)
  (q : Q ⟶ (relativeProj B).scheme) (e : C ⟶ ψ.relativeMapDomain.toScheme)
  (ha : a ≫ p = e ≫ relativeMapHom ψ) (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι)

/-- The inverse image of the multiplication of a sheaf of graded algebras, read through
Stacks 01CD, is the multiplication of the inverse image. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf {W Z : Scheme.{u}} (g : W ⟶ Z)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Z.toRingedSpace))
    (i j : ℤ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g (G.piece i) (G.piece j)).inv ≫
        (Scheme.Modules.pullback g).map (SheafOfModules.GradedAlgebra.mulSheaf G i j) =
      SheafOfModules.GradedAlgebra.mulSheaf (pbAlgS g G) i j := by
  rw [Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra g.toLRSHom.toShHom G i j]
  rfl

/-- **`θ` of Tag 07ZG read on a chart carries the pulled-back multiplication of the twists to the
pulled-back multiplication**: the degree-wise maps `a^*p^*𝒪(n) ⟶ b^*q^*𝒪(n)` of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom` carry the multiplication of
`p^*(⨁_n 𝒪(n))`, pulled back along `a` and read through Stacks 01CD, to that of
`q^*(⨁_n 𝒪(n))` pulled back along `b`. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTwistAlgebraHom
    (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B)))
    (t : ∀ n : ℤ, (Scheme.Modules.pullback a).obj ((pbAlgS p (twistAlgebra A)).piece n) ⟶
      (Scheme.Modules.pullback b).obj ((pbAlgS q (twistAlgebra B)).piece n))
    (ht : ∀ n, t n = (chartTwistAlgebraHom ψ a b p q e ha hb θ).app n) (i j : ℤ) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso a
        ((pbAlgS p (twistAlgebra A)).piece i) ((pbAlgS p (twistAlgebra A)).piece j)).inv ≫
        (Scheme.Modules.pullback a).map
          (SheafOfModules.GradedAlgebra.mulSheaf (pbAlgS p (twistAlgebra A)) i j) ≫ t (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨C.toRingedSpace.presheaf, C.toRingedSpace.IsSheaf⟩)).map
        ((t i, t j) : (_, _) ⟶ (_, _)) ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso b
          ((pbAlgS q (twistAlgebra B)).piece i) ((pbAlgS q (twistAlgebra B)).piece j)).inv ≫
        (Scheme.Modules.pullback b).map
          (SheafOfModules.GradedAlgebra.mulSheaf (pbAlgS q (twistAlgebra B)) i j) := by
  obtain rfl : t = _ := funext ht
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (pullbackTensorIso_inv_comp_map_mulSheaf a (pbAlgS p (twistAlgebra A)) i j))).trans ?_
  refine (AlgebraicGeometry.Space.mulSheaf_comp_tensorSheafMap_of_hom
    (chartTwistAlgebraHom ψ a b p q e ha hb θ) i j).trans ?_
  exact congrArg (_ ≫ ·)
    (pullbackTensorIso_inv_comp_map_mulSheaf b (pbAlgS q (twistAlgebra B)) i j).symm

end Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

attribute [local irreducible] CategoryTheory.yoneda

/-! ### Multiplicativity from two chart readings -/

section Abstract

variable {CG CU : Type*} [Category CG] [MonoidalCategory CG] [Category CU] [MonoidalCategory CU]
  (F : CG ⥤ CU)

/-- **Multiplicativity from two chart readings.**  Let `F` be faithful on morphisms
`A_i ⊗ A_j ⟶ B_k`, `m_A`, `m_B` multiplications read through `F` and chart identifications `κ`,
`ρ` as `μ_L`, `μ_{L'}`, and `θ_n : A_n ⟶ B_n` read as `ϑ_n : L_n ⟶ L'_n`.  If the `ϑ` carry `μ_L`
to `μ_{L'}`, the `θ` carry `m_A` to `m_B`. -/
theorem mul_comp_eq_of_two_chart_readings {Ai Aj Ak Bi Bj Bk : CG} (mA : Ai ⊗ Aj ⟶ Ak)
    (mB : Bi ⊗ Bj ⟶ Bk) (θi : Ai ⟶ Bi) (θj : Aj ⟶ Bj) (θk : Ak ⟶ Bk)
    (tA : F.obj (Ai ⊗ Aj) ⟶ F.obj Ai ⊗ F.obj Aj) (tB : F.obj (Bi ⊗ Bj) ⟶ F.obj Bi ⊗ F.obj Bj)
    (htnat : F.map (θi ⊗ₘ θj) ≫ tB = tA ≫ (F.map θi ⊗ₘ F.map θj))
    {Li Lj Lk L'i L'j L'k : CU} (κi : F.obj Ai ⟶ Li) (κj : F.obj Aj ⟶ Lj) (κk : F.obj Ak ⟶ Lk)
    (μL : Li ⊗ Lj ⟶ Lk) (ρi : F.obj Bi ⟶ L'i) (ρj : F.obj Bj ⟶ L'j) (ρk : F.obj Bk ≅ L'k)
    (μL' : L'i ⊗ L'j ⟶ L'k) (ϑi : Li ⟶ L'i) (ϑj : Lj ⟶ L'j) (ϑk : Lk ⟶ L'k)
    (hA : F.map mA ≫ κk = tA ≫ (κi ⊗ₘ κj) ≫ μL)
    (hB : F.map mB ≫ ρk.hom = tB ≫ (ρi ⊗ₘ ρj) ≫ μL')
    (hi : F.map θi ≫ ρi = κi ≫ ϑi) (hj : F.map θj ≫ ρj = κj ≫ ϑj)
    (hk : F.map θk ≫ ρk.hom = κk ≫ ϑk) (hϑ : (ϑi ⊗ₘ ϑj) ≫ μL' = μL ≫ ϑk)
    (hinj : ∀ φ ψ : Ai ⊗ Aj ⟶ Bk, F.map φ = F.map ψ → φ = ψ) :
    mA ≫ θk = (θi ⊗ₘ θj) ≫ mB := by
  refine hinj _ _ ?_
  rw [← cancel_mono ρk.hom, F.map_comp, F.map_comp, Category.assoc, Category.assoc, hk, hB,
    reassoc_of% hA, reassoc_of% htnat, ← hϑ, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc, hi, hj]

/-- A multiplication read along a square of functors: if `cμ` is read through `κ` as `μ_K`, `μ_K`
is read through `G` and `ℓ` as `μ_L`, and `s` is natural in `μ` and compatible with the tensor
identifications, then `F (tH⁻¹ ≫ H μ)` is read through `s`, `G κ` and `ℓ` as `μ_L`. -/
theorem map_mul_comp_reading_of_square {CP CU' : Type*} [Category CP] [MonoidalCategory CP]
    [Category CU'] [MonoidalCategory CU'] (H : CP ⥤ CG) (G : CU' ⥤ CU)
    {Ti Tj Tk : CP} (μ : Ti ⊗ Tj ⟶ Tk) (tH : H.obj (Ti ⊗ Tj) ≅ H.obj Ti ⊗ H.obj Tj)
    {cTi cTj cTij cTk Ki Kj Kk : CU'} (tc : cTij ⟶ cTi ⊗ cTj) (cμ : cTij ⟶ cTk)
    (κi : cTi ⟶ Ki) (κj : cTj ⟶ Kj) (κk : cTk ⟶ Kk) (μK : Ki ⊗ Kj ⟶ Kk)
    (hμ : cμ ≫ κk = tc ≫ (κi ⊗ₘ κj) ≫ μK)
    {Li Lj Lk : CU} (ℓi : G.obj Ki ⟶ Li) (ℓj : G.obj Kj ⟶ Lj) (ℓk : G.obj Kk ⟶ Lk)
    (μL : Li ⊗ Lj ⟶ Lk) (tY : G.obj (Ki ⊗ Kj) ⟶ G.obj Ki ⊗ G.obj Kj)
    (tY' : G.obj (cTi ⊗ cTj) ⟶ G.obj cTi ⊗ G.obj cTj)
    (hnY : G.map (κi ⊗ₘ κj) ≫ tY = tY' ≫ (G.map κi ⊗ₘ G.map κj))
    (hℓ : G.map μK ≫ ℓk = tY ≫ (ℓi ⊗ₘ ℓj) ≫ μL)
    (si : F.obj (H.obj Ti) ⟶ G.obj cTi) (sj : F.obj (H.obj Tj) ⟶ G.obj cTj)
    (sij : F.obj (H.obj (Ti ⊗ Tj)) ⟶ G.obj cTij) (sk : F.obj (H.obj Tk) ⟶ G.obj cTk)
    (hnat : F.map (H.map μ) ≫ sk = sij ≫ G.map cμ)
    (tF : F.obj (H.obj Ti ⊗ H.obj Tj) ⟶ F.obj (H.obj Ti) ⊗ F.obj (H.obj Tj))
    (hsq : F.map tH.hom ≫ tF ≫ (si ⊗ₘ sj) = sij ≫ G.map tc ≫ tY') :
    F.map (tH.inv ≫ H.map μ) ≫ sk ≫ G.map κk ≫ ℓk =
      tF ≫ ((si ≫ G.map κi ≫ ℓi) ⊗ₘ (sj ≫ G.map κj ≫ ℓj)) ≫ μL := by
  have h1 : F.map tH.inv ≫ sij ≫ G.map tc ≫ tY' = tF ≫ (si ⊗ₘ sj) := by
    rw [← hsq, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [F.map_comp, Category.assoc, reassoc_of% hnat, ← G.map_comp_assoc, hμ, G.map_comp,
    G.map_comp, Category.assoc, Category.assoc, hℓ, reassoc_of% hnY, reassoc_of% h1]
  simp only [tensorHom_comp_tensorHom_assoc]

end Abstract

/-! ### The inverse image of a pulled-back multiplication, read along a square -/

section Square

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
  (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c)

/-- **The inverse image along `c''` of a multiplication pulled back along `h`, read along the
square `c'' ≫ h = Y ≫ c`**: if `μ` is read along `c` through `κ` as `μ_K` and `μ_K` along `Y`
through `ℓ` as `μ_L`, then `(h^*μ)` read through Stacks 03EL is read along `c''` through the
identification along the square followed by `Y^*κ` and `ℓ`, as `μ_L`. -/
theorem modulePullback_map_pullbackTensorIso_inv_comp_reading
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
      (modulePullbackTensorIso B S hS Y Ki Kj).hom ≫ (ℓi ⊗ₘ ℓj) ≫ μL) :
    (modulePullback B S hS c'').map
        ((modulePullbackTensorIso B S hS h Ti Tj).inv ≫ (modulePullback B S hS h).map μ) ≫
        pullbackSquareHom c'' c h Y hY Tk ≫ (modulePullback B S hS Y).map κk ≫ ℓk =
      (modulePullbackTensorIso B S hS c'' _ _).hom ≫
        ((pullbackSquareHom c'' c h Y hY Ti ≫ (modulePullback B S hS Y).map κi ≫ ℓi) ⊗ₘ
          (pullbackSquareHom c'' c h Y hY Tj ≫ (modulePullback B S hS Y).map κj ≫ ℓj)) ≫ μL :=
  map_mul_comp_reading_of_square (modulePullback B S hS c'') (modulePullback B S hS h)
    (modulePullback B S hS Y) μ (modulePullbackTensorIso B S hS h Ti Tj)
    (modulePullbackTensorIso B S hS c Ti Tj).hom ((modulePullback B S hS c).map μ) κi κj κk μK
    hμ ℓi ℓj ℓk μL (modulePullbackTensorIso B S hS Y Ki Kj).hom
    (modulePullbackTensorIso B S hS Y _ _).hom
    (modulePullbackTensorIso_hom_naturality B S hS Y κi κj) hℓ
    (pullbackSquareHom c'' c h Y hY Ti) (pullbackSquareHom c'' c h Y hY Tj)
    (pullbackSquareHom c'' c h Y hY (Ti ⊗ Tj)) (pullbackSquareHom c'' c h Y hY Tk)
    (pullbackSquareHom_naturality c'' c h Y hY μ) (modulePullbackTensorIso B S hS c'' _ _).hom
    (pullbackSquareHom_tensor c'' c h Y hY Ti Tj)

end Square


/-! ### Attached multiplications and units -/

section Attached

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A bifunctor carries a pair of identities to the identity. -/
theorem bifunctor_map_id_comp_map_id {C D : Type*} [Category C] [Category D] (F : C ⥤ C ⥤ D)
    (M N : C) : (F.map (𝟙 M)).app N ≫ (F.obj M).map (𝟙 N) = 𝟙 _ := by
  simp

/-- The tensor product of two identities of quasi-coherent modules is the identity. -/
theorem quasicoherentTensorHom_id_id (U : BigFppfOver B S hS)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentTensorHom B S hS U (𝟙 M) (𝟙 N) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (bifunctor_map_id_comp_map_id _ M.obj N.obj)

/-- For isomorphisms `α`, `β` with `g ≫ β.hom = α.hom ≫ f` and a square `g ≫ Fm' = Fm ≫ Fc`,
`f ≫ β.inv ≫ Fm' = (α.inv ≫ Fm) ≫ Fc`. -/
theorem comp_inv_comp_eq_of_naturality {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (α : X ≅ Y) (β : X' ≅ Y') (f : Y ⟶ Y') (g : X ⟶ X') (hn : g ≫ β.hom = α.hom ≫ f)
    (Fm : X ⟶ Z) (Fm' : X' ⟶ Z') (Fc : Z ⟶ Z') (hF : g ≫ Fm' = Fm ≫ Fc) :
    f ≫ β.inv ≫ Fm' = (α.inv ≫ Fm) ≫ Fc := by
  have h : f ≫ β.inv = α.inv ≫ g := by
    rw [Iso.comp_inv_eq, Category.assoc, hn, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, hF, Category.assoc]

/-- **The attached multiplication is natural**: for `a ⊗ b` followed by `m'` equal to `m`
followed by `c`, the attached morphisms satisfy the same equation. -/
theorem representedTensorChartMul_naturality {U : BigFppfOver B S hS}
    {M M' N N' K K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (a : M ⟶ M') (b : N ⟶ N') (c : K ⟶ K') (m : quasicoherentTensorObj B S hS U M N ⟶ K)
    (m' : quasicoherentTensorObj B S hS U M' N' ⟶ K')
    (h : quasicoherentTensorHom B S hS U a b ≫ m' = m ≫ c) :
    MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map a).hom
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map b).hom ≫
        representedTensorChartMul B S hS m' =
      representedTensorChartMul B S hS m ≫
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map c).hom :=
  comp_inv_comp_eq_of_naturality (representedQuasicoherentSchemeTensorIso B S hS U M N)
    (representedQuasicoherentSchemeTensorIso B S hS U M' N') _ _
    (representedQuasicoherentSchemeTensorIso_hom_naturality B S hS U a b) _ _ _
    (congrArg (fun z => z.hom)
      (((representedQuasicoherentSchemeEquivalence B S hS U).functor.map_comp _ _).symm.trans
        ((congrArg (representedQuasicoherentSchemeEquivalence B S hS U).functor.map h).trans
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map_comp _ _))))

/-- An equation with three trailing identities is the equation without them. -/
theorem comp_comp_tensor_comp_of_ids {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z W₁ W₂ V₁ V₂ : C} (A : X ⟶ Y) (B' : Y ⟶ Z) (iK : Z ⟶ Z) (heK : iK = 𝟙 Z)
    (T : X ⟶ W₁ ⊗ W₂) (B₁ : W₁ ⟶ V₁) (i₁ : V₁ ⟶ V₁) (he₁ : i₁ = 𝟙 V₁) (B₂ : W₂ ⟶ V₂)
    (i₂ : V₂ ⟶ V₂) (he₂ : i₂ = 𝟙 V₂) (D : V₁ ⊗ V₂ ⟶ Z)
    (h : A ≫ B' ≫ iK = T ≫ ((B₁ ≫ i₁) ⊗ₘ (B₂ ≫ i₂)) ≫ D) :
    A ≫ B' = T ≫ (B₁ ⊗ₘ B₂) ≫ D := by
  subst heK he₁ he₂
  simpa only [Category.comp_id] using h

/-- `f ≫ g ≫ 𝟙 = t ≫ f ≫ g` for `t = 𝟙`. -/
theorem comp_comp_id_eq_comp_of_eq_id {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (t : X ⟶ X) (ht : t = 𝟙 X) : f ≫ g ≫ 𝟙 Z = t ≫ f ≫ g := by
  subst ht
  simp only [Category.comp_id, Category.id_comp]

/-- **The inverse image of an attached multiplication along a morphism of the site is the attached
multiplication of the pulled-back multiplication**, through the identifications of Stacks 03DX (2)
and Stacks 03EL. -/
theorem modulePullback_map_representedTensorChartMul_pullback {V U : BigFppfOver B S hS}
    (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedTensorChartMul B S hS m) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    (modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom ≫
      ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ⊗ₘ
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom) ≫
      representedTensorChartMul B S hS
        ((quasicoherentPullbackTensorIso B S hS g M N).inv ≫ quasicoherentPullbackMap B S hS g m) :=
  comp_comp_tensor_comp_of_ids (C := Modules.{u, u} B S hS (yoneda.obj V)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)) _ _ _
    (representedQuasicoherentSchemeEquivalence_map_id_hom B S hS (k := g) K) _ _ _
    (representedQuasicoherentSchemeEquivalence_map_id_hom B S hS (k := g) M) _ _
    (representedQuasicoherentSchemeEquivalence_map_id_hom B S hS (k := g) N) _
    (modulePullback_map_representedTensorChartMul_comp B S hS g m
      ((quasicoherentPullbackTensorIso B S hS g M N).inv ≫ quasicoherentPullbackMap B S hS g m)
      (𝟙 _) (𝟙 _) (𝟙 _) (representedC3TensorCompat B S hS g M N)
      (comp_comp_id_eq_comp_of_eq_id _ _ _ (quasicoherentTensorHom_id_id V _ _)))

end Attached

/-! ### The chart identification `atlasPullbackChartIso`, written along the square -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  {Y : AlgebraicSpaces B S hS} (f : Y ⟶ ⟨P, hP⟩) (P' : Presentation B S hS Y.1 Y.2)
  (fU : P'.U ⟶ d.fibre Px.U Px.toSpace)
  (hsq : P'.atlas ≫ f = representedSpaceMap B S hS fU ≫
    presentationAtlas (d.spacePresentation Px hP))
  (D : Modules.{u, u} B S hS P hP)
  (M : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (c : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj D ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
      M).obj)

/-- The canonical comparison of two inverse images along a square is the identification along the
square. -/
theorem canonicalComparison_hom_eq_pullbackSquareHom {A P' Q' R : AlgebraicSpaces B S hS}
    (a : P' ⟶ Q') (b : P' ⟶ R) (fi : Q' ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    (QuasiCoherentDescent.canonicalComparison a b fi fj h N).hom =
      pullbackSquareHom a fj fi b h N :=
  (canonicalComparison_hom_eq_compIso B S hS a b fi fj h N).trans
    (pullbackSquareHom_eq_comp a fj fi b h N).symm

/-- **The chart identification `AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`
is the identification along the square**, followed by the inverse image of the chart
identification of `𝒟` and Stacks 03DX (2). -/
theorem atlasPullbackChartIso_hom_eq :
    (atlasPullbackChartIso d Px hP f P' fU hsq D M c).hom =
      pullbackSquareHom (U'' := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
          P'.atlas (presentationAtlas (d.spacePresentation Px hP)) f
          (representedSpaceMap B S hS fU) hsq D ≫
        (modulePullback B S hS (representedSpaceMap B S hS fU)).map c.hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS fU M).hom :=
  congrArg (fun z => z ≫ (modulePullback B S hS (representedSpaceMap B S hS fU)).map c.hom ≫
    (modulePullbackRepresentedQuasicoherentIso B S hS fU M).hom)
    (canonicalComparison_hom_eq_pullbackSquareHom
      (P' := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩) P'.atlas
      (representedSpaceMap B S hS fU) f (presentationAtlas (d.spacePresentation Px hP)) hsq D)

variable {Di Dj : Modules.{u, u} B S hS P hP}
  {Mi Mj : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (ci : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj Di ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
      Mi).obj)
  (cj : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj Dj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
      Mj).obj)

omit hsq in
/-- A reading `A ≫ κ_k = T ≫ (κ_i ⊗ κ_j) ≫ m` transported along equations of the `κ`. -/
theorem reading_congr {C : Type*} [Category C] [MonoidalCategory C] {X₀ Ki Kj Kk Li Lj Lk : C}
    {A : X₀ ⟶ Kk} {T : X₀ ⟶ Ki ⊗ Kj} {κi κi' : Ki ⟶ Li} {κj κj' : Kj ⟶ Lj} {κk κk' : Kk ⟶ Lk}
    {m : Li ⊗ Lj ⟶ Lk} (h : A ≫ κk' = T ≫ (κi' ⊗ₘ κj') ≫ m) (hk : κk = κk') (hi : κi = κi')
    (hj : κj = κj') : A ≫ κk = T ≫ (κi ⊗ₘ κj) ≫ m := by
  subst hk hi hj
  exact h

/-- **A multiplication read on the chart of `P`, pulled back along `f`, is read on the atlas of `Y`
through the chart identifications
`AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`** as the pulled-back attached
multiplication. -/
theorem atlasPullbackChartIso_mul_reading (μ : Di ⊗ Dj ⟶ D)
    (m : quasicoherentTensorObj B S hS (d.fibre Px.U Px.toSpace) Mi Mj ⟶ M)
    (hμ : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map μ ≫ c.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (d.spacePresentation Px hP)) Di
        Dj).hom ≫ (ci.hom ⊗ₘ cj.hom) ≫ representedTensorChartMul B S hS m) :
    (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).map ((modulePullbackTensorIso B S hS f Di Dj).inv ≫
          (modulePullback B S hS f).map μ) ≫
        (atlasPullbackChartIso d Px hP f P' fU hsq D M c).hom =
      (modulePullbackTensorIso B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
          P'.atlas _ _).hom ≫
        ((atlasPullbackChartIso d Px hP f P' fU hsq Di Mi ci).hom ⊗ₘ
          (atlasPullbackChartIso d Px hP f P' fU hsq Dj Mj cj).hom) ≫
        representedTensorChartMul B S hS
          ((quasicoherentPullbackTensorIso B S hS fU Mi Mj).inv ≫
            quasicoherentPullbackMap B S hS fU m) := by
  refine reading_congr (C := Modules.{u, u} B S hS (yoneda.obj P'.U)
      (isAlgebraicSpace_yoneda B S hS P'.U)) ?_
    (atlasPullbackChartIso_hom_eq d Px hP f P' fU hsq D M c)
    (atlasPullbackChartIso_hom_eq d Px hP f P' fU hsq Di Mi ci)
    (atlasPullbackChartIso_hom_eq d Px hP f P' fU hsq Dj Mj cj)
  exact (modulePullback_map_pullbackTensorIso_inv_comp_reading
    (U'' := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩) P'.atlas
    (presentationAtlas (d.spacePresentation Px hP)) f
    (representedSpaceMap B S hS fU) hsq μ ci.hom cj.hom c.hom
    (representedTensorChartMul B S hS m) hμ
    (modulePullbackRepresentedQuasicoherentIso B S hS fU Mi).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS fU Mj).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS fU M).hom _
    (modulePullback_map_representedTensorChartMul_pullback fU m) :)

end RelativeProjPoints


/-! ### Multiplicativity from chart readings, along a morphism of algebraic spaces -/

section ModulesAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G U : AlgebraicSpaces B S hS} (c : U ⟶ G)

/-- `AlgebraicGeometry.Space.mul_comp_eq_of_two_chart_readings` for the inverse image along a
morphism `c` of algebraic spaces, read through Stacks 03EL. -/
theorem mul_comp_eq_of_two_pullback_readings {Ai Aj Ak Bi Bj Bk : Modules.{u, u} B S hS G.1 G.2}
    (mA : Ai ⊗ Aj ⟶ Ak) (mB : Bi ⊗ Bj ⟶ Bk) (θi : Ai ⟶ Bi) (θj : Aj ⟶ Bj) (θk : Ak ⟶ Bk)
    {Li Lj Lk L'i L'j L'k : Modules.{u, u} B S hS U.1 U.2}
    (κi : (modulePullback B S hS c).obj Ai ⟶ Li) (κj : (modulePullback B S hS c).obj Aj ⟶ Lj)
    (κk : (modulePullback B S hS c).obj Ak ⟶ Lk) (μL : Li ⊗ Lj ⟶ Lk)
    (ρi : (modulePullback B S hS c).obj Bi ⟶ L'i) (ρj : (modulePullback B S hS c).obj Bj ⟶ L'j)
    (ρk : (modulePullback B S hS c).obj Bk ≅ L'k) (μL' : L'i ⊗ L'j ⟶ L'k)
    (ϑi : Li ⟶ L'i) (ϑj : Lj ⟶ L'j) (ϑk : Lk ⟶ L'k)
    (hA : (modulePullback B S hS c).map mA ≫ κk =
      (modulePullbackTensorIso B S hS c Ai Aj).hom ≫ (κi ⊗ₘ κj) ≫ μL)
    (hB : (modulePullback B S hS c).map mB ≫ ρk.hom =
      (modulePullbackTensorIso B S hS c Bi Bj).hom ≫ (ρi ⊗ₘ ρj) ≫ μL')
    (hi : (modulePullback B S hS c).map θi ≫ ρi = κi ≫ ϑi)
    (hj : (modulePullback B S hS c).map θj ≫ ρj = κj ≫ ϑj)
    (hk : (modulePullback B S hS c).map θk ≫ ρk.hom = κk ≫ ϑk)
    (hϑ : (ϑi ⊗ₘ ϑj) ≫ μL' = μL ≫ ϑk)
    (hinj : ∀ φ ψ : Ai ⊗ Aj ⟶ Bk,
      (modulePullback B S hS c).map φ = (modulePullback B S hS c).map ψ → φ = ψ) :
    mA ≫ θk = (θi ⊗ₘ θj) ≫ mB :=
  mul_comp_eq_of_two_chart_readings (modulePullback B S hS c) mA mB θi θj θk
    (modulePullbackTensorIso B S hS c Ai Aj).hom (modulePullbackTensorIso B S hS c Bi Bj).hom
    (modulePullbackTensorIso_hom_naturality B S hS c θi θj) κi κj κk μL ρi ρj ρk μL' ϑi ϑj ϑk
    hA hB hi hj hk hϑ hinj

end ModulesAssembly

/-! ### Multiplicativity over a presentation, for two morphisms to relative Projs -/

section PairAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} (dP : RelativeProjPoints B S hS πP) (dQ : RelativeProjPoints B S hS πQ)
  (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  {G : AlgebraicSpaces B S hS} (r : G ⟶ ⟨P, hP⟩) (ι : G ⟶ ⟨Q, hQ⟩)
  (P' : Presentation B S hS G.1 G.2)
  (fP : P'.U ⟶ dP.fibre Px.U Px.toSpace) (fQ : P'.U ⟶ dQ.fibre Px.U Px.toSpace)
  (hsqP : P'.atlas ≫ r = representedSpaceMap B S hS fP ≫
    presentationAtlas (dP.spacePresentation Px hP))
  (hsqQ : P'.atlas ≫ ι = representedSpaceMap B S hS fQ ≫
    presentationAtlas (dQ.spacePresentation Px hQ))
  {D₁i D₁j D₁k : Modules.{u, u} B S hS P hP}
  {M₁i M₁j M₁k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (c₁i : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁i ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁i).obj)
  (c₁j : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁j ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁j).obj)
  (c₁k : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁k ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁k).obj)
  {D₂i D₂j D₂k : Modules.{u, u} B S hS Q hQ}
  {M₂i M₂j M₂k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (c₂i : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂i ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂i).obj)
  (c₂j : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂j ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂j).obj)
  (c₂k : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂k ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂k).obj)
  (θUi : quasicoherentPullbackObj B S hS fP M₁i ⟶ quasicoherentPullbackObj B S hS fQ M₂i)
  (θUj : quasicoherentPullbackObj B S hS fP M₁j ⟶ quasicoherentPullbackObj B S hS fQ M₂j)
  (θUk : quasicoherentPullbackObj B S hS fP M₁k ⟶ quasicoherentPullbackObj B S hS fQ M₂k)
  (χi : (modulePullback B S hS r).obj D₁i ⟶ (modulePullback B S hS ι).obj D₂i)
  (χj : (modulePullback B S hS r).obj D₁j ⟶ (modulePullback B S hS ι).obj D₂j)
  (χk : (modulePullback B S hS r).obj D₁k ⟶ (modulePullback B S hS ι).obj D₂k)

omit hsqP hsqQ in
/-- The inverse image along the atlas of a presentation is faithful. -/
theorem modulePullback_atlas_map_injective {M N : Modules.{u, u} B S hS G.1 G.2} (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).map φ =
      (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).map ψ) : φ = ψ :=
  QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering' B S hS φ ψ
    (Vi := fun _ : Unit => ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
    (fi := fun _ => P'.atlas) (fun _ => h)
    (isEtaleCovering_of_surjective_etale B S hS
      (Q := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩) P'.atlas
      ((isEtale_iff_presheaf_of_yoneda B S hS P'.toSpace).2 P'.etale) P'.surjective)

/-- Morphisms `r^*𝒟₁ ⟶ ι^*𝒟₂` read on an atlas as chart maps carry multiplications to
multiplications, given the readings of the pulled-back multiplications on the atlas. -/
theorem mul_comp_of_atlasReadings
    (hχi : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂i M₂i c₂i)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁i M₁i c₁i).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUi).hom χi)
    (hχj : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂j M₂j c₂j)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁j M₁j c₁j).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUj).hom χj)
    (hχk : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂k M₂k c₂k)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁k M₁k c₁k).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUk).hom χk)
    (μ₁ : D₁i ⊗ D₁j ⟶ D₁k)
    (m₁ : quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) M₁i M₁j ⟶ M₁k)
    (μ₂ : D₂i ⊗ D₂j ⟶ D₂k)
    (m₂ : quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) M₂i M₂j ⟶ M₂k)
    (hA : (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).map ((modulePullbackTensorIso B S hS r D₁i D₁j).inv ≫
          (modulePullback B S hS r).map μ₁) ≫
        (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁k M₁k c₁k).hom =
      (modulePullbackTensorIso B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
          P'.atlas _ _).hom ≫
        ((RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁i M₁i c₁i).hom ⊗ₘ
          (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁j M₁j c₁j).hom) ≫
        representedTensorChartMul B S hS
          ((quasicoherentPullbackTensorIso B S hS fP M₁i M₁j).inv ≫
            quasicoherentPullbackMap B S hS fP m₁))
    (hB : (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).map ((modulePullbackTensorIso B S hS ι D₂i D₂j).inv ≫
          (modulePullback B S hS ι).map μ₂) ≫
        (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂k M₂k c₂k).hom =
      (modulePullbackTensorIso B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
          P'.atlas _ _).hom ≫
        ((RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂i M₂i c₂i).hom ⊗ₘ
          (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂j M₂j c₂j).hom) ≫
        representedTensorChartMul B S hS
          ((quasicoherentPullbackTensorIso B S hS fQ M₂i M₂j).inv ≫
            quasicoherentPullbackMap B S hS fQ m₂))
    (hθU : quasicoherentTensorHom B S hS P'.U θUi θUj ≫
        (quasicoherentPullbackTensorIso B S hS fQ M₂i M₂j).inv ≫
        quasicoherentPullbackMap B S hS fQ m₂ =
      ((quasicoherentPullbackTensorIso B S hS fP M₁i M₁j).inv ≫
        quasicoherentPullbackMap B S hS fP m₁) ≫ θUk) :
    (modulePullbackTensorIso B S hS r D₁i D₁j).inv ≫ (modulePullback B S hS r).map μ₁ ≫ χk =
      (χi ⊗ₘ χj) ≫ (modulePullbackTensorIso B S hS ι D₂i D₂j).inv ≫
        (modulePullback B S hS ι).map μ₂ :=
  (Category.assoc _ _ _).symm.trans (mul_comp_eq_of_two_pullback_readings
    (U := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩) P'.atlas
    _ _ χi χj χk _ _ _ _ _ _
    (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂k M₂k c₂k) _ _ _ _
    hA hB hχi hχj hχk (representedTensorChartMul_naturality θUi θUj θUk _ _ hθU)
    (fun φ ψ h => modulePullback_atlas_map_injective P' φ ψ h))

/-- **Morphisms `r^*𝒟₁ ⟶ ι^*𝒟₂` read on an atlas as chart maps carry multiplications to
multiplications**: for `r : G ⟶ P`, `ι : G ⟶ Q` and a presentation of `G` whose atlas lies over the
charts of `P` and `Q`, if `χ_n` is `θ_{U,n}` on the atlas through the chart identifications
`AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`, the multiplications `μ₁`, `μ₂`
are read on the charts of `P` and `Q` as attached multiplications `m₁`, `m₂`, and the `θ_U` carry
the pulled-back `m₁` to the pulled-back `m₂`, then the `χ` carry `r^*μ₁` to `ι^*μ₂`, both read
through Stacks 03EL. -/
theorem mul_comp_of_isAtlasMapComp
    (hχi : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂i M₂i c₂i)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁i M₁i c₁i).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUi).hom χi)
    (hχj : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂j M₂j c₂j)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁j M₁j c₁j).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUj).hom χj)
    (hχk : Presentation.IsAtlasMapComp (X := G) P'
      (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ ι P' fQ hsqQ D₂k M₂k c₂k)
      (RelativeProjPoints.atlasPullbackChartIso dP Px hP r P' fP hsqP D₁k M₁k c₁k).hom
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θUk).hom χk)
    (μ₁ : D₁i ⊗ D₁j ⟶ D₁k)
    (m₁ : quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) M₁i M₁j ⟶ M₁k)
    (hμ₁ : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).map μ₁ ≫
        c₁k.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (dP.spacePresentation Px hP)) D₁i
        D₁j).hom ≫ (c₁i.hom ⊗ₘ c₁j.hom) ≫ representedTensorChartMul B S hS m₁)
    (μ₂ : D₂i ⊗ D₂j ⟶ D₂k)
    (m₂ : quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) M₂i M₂j ⟶ M₂k)
    (hμ₂ : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).map μ₂ ≫
        c₂k.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (dQ.spacePresentation Px hQ)) D₂i
        D₂j).hom ≫ (c₂i.hom ⊗ₘ c₂j.hom) ≫ representedTensorChartMul B S hS m₂)
    (hθU : quasicoherentTensorHom B S hS P'.U θUi θUj ≫
        (quasicoherentPullbackTensorIso B S hS fQ M₂i M₂j).inv ≫
        quasicoherentPullbackMap B S hS fQ m₂ =
      ((quasicoherentPullbackTensorIso B S hS fP M₁i M₁j).inv ≫
        quasicoherentPullbackMap B S hS fP m₁) ≫ θUk) :
    (modulePullbackTensorIso B S hS r D₁i D₁j).inv ≫ (modulePullback B S hS r).map μ₁ ≫ χk =
      (χi ⊗ₘ χj) ≫ (modulePullbackTensorIso B S hS ι D₂i D₂j).inv ≫
        (modulePullback B S hS ι).map μ₂ :=
  mul_comp_of_atlasReadings dP dQ Px hP hQ r ι P' fP fQ hsqP hsqQ c₁i c₁j c₁k c₂i c₂j c₂k
    θUi θUj θUk χi χj χk hχi hχj hχk μ₁ m₁ μ₂ m₂
    (RelativeProjPoints.atlasPullbackChartIso_mul_reading dP Px hP r P' fP hsqP D₁k M₁k c₁k
      c₁i c₁j μ₁ m₁ hμ₁)
    (RelativeProjPoints.atlasPullbackChartIso_mul_reading dQ Px hQ ι P' fQ hsqQ D₂k M₂k c₂k
      c₂i c₂j μ₂ m₂ hμ₂) hθU

end PairAssembly

/-! ### `θ` on a chart of `U(ψ)`, and multiplicativity over a presentation -/

namespace RelativeProjHomPoints

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ)

/-- A morphism framed by the images of two identities is itself. -/
theorem map_refl_hom_comp_comp_map_refl_inv {C C' D : Type*} [Category C] [Category C']
    [Category D] (F : C ⥤ D) (G : C' ⥤ D) (X : C) (Y : C') (x : F.obj X ⟶ G.obj Y) :
    F.map (Iso.refl X).hom ≫ x ≫ G.map (Iso.refl Y).inv = x := by
  simp

section ChartMul

variable (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj)
  (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
  (hp : p = (dP.fibreIso T f).hom)
  (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
  (hq : q = (dQ.fibreIso T f).hom)
  (hM₁ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dP.fibre T f)).ringCatSheaf
    ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
  (hM₂ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dQ.fibre T f)).ringCatSheaf
    ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))

/-- The twist `𝒪(n)` of `P ×_X T`, as the inverse image of the twist of Tag 01NR. -/
abbrev chartReflSourcePiece (n : ℤ) :
    (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback p).obj
    ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n), hM₁ n⟩

/-- The twist `𝒪(n)` of `Q ×_X T`, as the inverse image of the twist of Tag 01NR. -/
abbrev chartReflTargetPiece (n : ℤ) :
    (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback q).obj
    ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n), hM₂ n⟩

/-- The chart map `θ_n` with the identity identifications of the twists. -/
abbrev chartTwistMapRefl (n : ℤ) :
    quasicoherentPullbackObj B S hS (hψ.chartMapHom T f) (chartReflSourcePiece T f p hM₁ n) ⟶
      quasicoherentPullbackObj B S hS (hψ.chartIncl T f) (chartReflTargetPiece T f q hM₂ n) :=
  hψ.chartTwistMap T f n
    (M₁ := ⟨(Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n), hM₁ n⟩) p hp
    (Iso.refl ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
    (M₂ := ⟨(Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n), hM₂ n⟩) q hq
    (Iso.refl ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))

/-- The underlying morphism of the chart map `θ_n` with the identity identifications is the
degree-`n` component of `θ` of Tag 07ZG read on the chart. -/
theorem chartTwistMapRefl_hom (n : ℤ) :
    (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ n).hom =
      (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom (hψ.hom T f)
        ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
        ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
        (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
        (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f))).app n :=
  (hψ.chartTwistMap_hom_eq_chartTwistAlgebraHom_app T f n
    (M₁ := ⟨(Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n), hM₁ n⟩) p hp
    (Iso.refl ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
    (M₂ := ⟨(Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n), hM₂ n⟩) q hq
    (Iso.refl ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))).trans
    (map_refl_hom_comp_comp_map_refl_inv _ _ _ _ _)

/-- **The chart maps `θ_n` carry the pulled-back multiplication of the twists of `P ×_X T` to the
pulled-back multiplication of the twists of `Q ×_X T`.** -/
theorem chartTwistMapRefl_mul (i j : ℤ)
    (m₁ : quasicoherentTensorObj B S hS (dP.fibre T f) (chartReflSourcePiece T f p hM₁ i)
      (chartReflSourcePiece T f p hM₁ j) ⟶ (chartReflSourcePiece T f p hM₁ (i + j)))
    (hm₁ : m₁ = ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
      (pbAlgS p (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f))) i j))
    (m₂ : quasicoherentTensorObj B S hS (dQ.fibre T f) (chartReflTargetPiece T f q hM₂ i)
      (chartReflTargetPiece T f q hM₂ j) ⟶ (chartReflTargetPiece T f q hM₂ (i + j)))
    (hm₂ : m₂ = ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
      (pbAlgS q (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f))) i j)) :
    quasicoherentTensorHom B S hS (hψ.chartObj T f)
        (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ i)
        (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ j) ≫
      (quasicoherentPullbackTensorIso B S hS (hψ.chartIncl T f) (chartReflTargetPiece T f q hM₂ i)
        (chartReflTargetPiece T f q hM₂ j)).inv ≫
      quasicoherentPullbackMap B S hS (hψ.chartIncl T f) m₂ =
    ((quasicoherentPullbackTensorIso B S hS (hψ.chartMapHom T f)
        (chartReflSourcePiece T f p hM₁ i) (chartReflSourcePiece T f p hM₁ j)).inv ≫
      quasicoherentPullbackMap B S hS (hψ.chartMapHom T f) m₁) ≫
      hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ (i + j) := by
  subst hm₁ hm₂
  refine ObjectProperty.hom_ext _ ?_
  exact (Stacks.AlgebraicGeometry.Tag07ZGTwist.pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTwistAlgebraHom
    (hψ.hom T f) ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
    ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
    (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
    (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f))
    (fun n => (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ n).hom)
    (hψ.chartTwistMapRefl_hom T f p hp q hq hM₁ hM₂) i j).symm.trans (Category.assoc _ _ _).symm

end ChartMul

section Assembly

variable (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  {D₁i D₁j D₁k : Modules.{u, u} B S hS P hP}
  {M₁i M₁j M₁k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (c₁i : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁i ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁i).obj)
  (c₁j : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁j ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁j).obj)
  (c₁k : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁k ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁k).obj)
  {D₂i D₂j D₂k : Modules.{u, u} B S hS Q hQ}
  {M₂i M₂j M₂k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (c₂i : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂i ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂i).obj)
  (c₂j : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂j ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂j).obj)
  (c₂k : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂k ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂k).obj)
  (θUi : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁i ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂i)
  (θUj : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁j ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂j)
  (θUk : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁k ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂k)


include c₁i c₁j c₁k c₂i c₂j c₂k in
/-- **Morphisms `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` which are chart maps carry multiplications to multiplications**:
if `χ_n` is `θ_{U,n}` on the chart `U(ψ)_U`
(`AlgebraicGeometry.Space.RelativeProjHomPoints.IsChartHom`), the multiplications `μ₁`, `μ₂` are
read on the charts of `P` and `Q` as attached multiplications `m₁`, `m₂`, and the `θ_U` carry the
pulled-back `m₁` to the pulled-back `m₂`, then the `χ` carry `r_ψ^*μ₁` to `ι^*μ₂`, both read
through Stacks 03EL. -/
theorem mul_comp_of_isChartHom
    (χi : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj D₁i ⟶
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj D₂i)
    (χj : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj D₁j ⟶
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj D₂j)
    (χk : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj D₁k ⟶
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj D₂k)
    (hχi : hψ.IsChartHom Px hG hP hQ D₁i M₁i c₁i D₂i M₂i c₂i θUi χi)
    (hχj : hψ.IsChartHom Px hG hP hQ D₁j M₁j c₁j D₂j M₂j c₂j θUj χj)
    (hχk : hψ.IsChartHom Px hG hP hQ D₁k M₁k c₁k D₂k M₂k c₂k θUk χk)
    (μ₁ : D₁i ⊗ D₁j ⟶ D₁k)
    (m₁ : quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) M₁i M₁j ⟶ M₁k)
    (hμ₁ : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).map μ₁ ≫
        c₁k.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (dP.spacePresentation Px hP)) D₁i
        D₁j).hom ≫ (c₁i.hom ⊗ₘ c₁j.hom) ≫ representedTensorChartMul B S hS m₁)
    (μ₂ : D₂i ⊗ D₂j ⟶ D₂k)
    (m₂ : quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) M₂i M₂j ⟶ M₂k)
    (hμ₂ : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).map μ₂ ≫
        c₂k.hom =
      (modulePullbackTensorIso B S hS (presentationAtlas (dQ.spacePresentation Px hQ)) D₂i
        D₂j).hom ≫ (c₂i.hom ⊗ₘ c₂j.hom) ≫ representedTensorChartMul B S hS m₂)
    (hθU : quasicoherentTensorHom B S hS (hψ.chartObj Px.U Px.toSpace) θUi θUj ≫
        (quasicoherentPullbackTensorIso B S hS (hψ.chartIncl Px.U Px.toSpace) M₂i M₂j).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartIncl Px.U Px.toSpace) m₂ =
      ((quasicoherentPullbackTensorIso B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁i M₁j).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartMapHom Px.U Px.toSpace) m₁) ≫ θUk) :
    (modulePullbackTensorIso B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
        D₁i D₁j).inv ≫
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).map μ₁ ≫
        χk =
      (χi ⊗ₘ χj) ≫ (modulePullbackTensorIso B S hS (ObjectProperty.homMk
        hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
        D₂i D₂j).inv ≫
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).map μ₂ :=
  mul_comp_of_isAtlasMapComp dP dQ Px hP hQ (ObjectProperty.homMk hψ.relativeMapSpaceHom :
      (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
    (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
      (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
    (hψ.presentationOfBase Px hG)
    (hψ.chartMapHom Px.U Px.toSpace) (hψ.chartIncl Px.U Px.toSpace)
    (hψ.presentationOfBase_atlas_comp_relativeMapSpaceHom Px hG hP)
    (hψ.presentationOfBase_atlas_comp_relativeMapSubfunctor_ι Px hG hQ) c₁i c₁j c₁k c₂i c₂j c₂k
    θUi θUj θUk χi χj χk hχi hχj hχk μ₁ m₁ hμ₁ μ₂ m₂ hμ₂ hθU

end Assembly


end RelativeProjHomPoints


/-! ### `θ` of Stacks 085F is multiplicative -/

namespace RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)

/-- The multiplication of the twists on the scheme of `V ×_X P` is the multiplication of the
inverse image of Tag 01NR's `⨁_n 𝒪(n)`. -/
theorem twistPieceMul_eq_homMk (s : RelativeProjSituation.{u, m})
    (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1) (i j : ℤ) :
    s.twistPieceMul V v i j =
      (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (pbAlgS (s.toRelativeProj V v)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.relativeProjPoints.algebra V v)))
          i j) :
        quasicoherentTensorObj s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
          (s.twistPieceQcoh V v i) (s.twistPieceQcoh V v j) ⟶ s.twistPieceQcoh V v (i + j)) :=
  rfl

section Map

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (Px : Presentation B S hS X.1 X.2)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **The chart maps `θ_n` of Tag 07ZG carry the pulled-back multiplication of the twists of
`P ×_X U` to that of `Q ×_X U`**, on the chart `U(ψ) ×_X U`. -/
theorem twistChartMap_mul (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ X.1) (i j : ℤ) :
    type_of% ((𝔥).chartTwistMapRefl_mul U u ((𝔰₁).toRelativeProj U u)
      ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u)
      ((𝔰₂).toRelativeProj U u) ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u)
      (fun n => ((𝔰₁).twistPieceQcoh U u n).2) (fun n => ((𝔰₂).twistPieceQcoh U u n).2) i j
      ((𝔰₁).twistPieceMul U u i j) ((𝔰₁).twistPieceMul_eq_homMk U u i j)
      ((𝔰₂).twistPieceMul U u i j) ((𝔰₂).twistPieceMul_eq_homMk U u i j)) :=
  (𝔥).chartTwistMapRefl_mul U u ((𝔰₁).toRelativeProj U u) ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u)
    ((𝔰₂).toRelativeProj U u) ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u)
    (fun n => ((𝔰₁).twistPieceQcoh U u n).2) (fun n => ((𝔰₂).twistPieceQcoh U u n).2) i j
    ((𝔰₁).twistPieceMul U u i j) ((𝔰₁).twistPieceMul_eq_homMk U u i j)
    ((𝔰₂).twistPieceMul U u i j) ((𝔰₂).twistPieceMul_eq_homMk U u i j)

end Map

end RelativeProjSituation

end AlgebraicGeometry.Space

end
