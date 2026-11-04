module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistAlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGradedMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeThetaGraded

/-!
# The maps `θ_d` of Stacks 085F carry multiplications to multiplications

For a map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`, with
`P = Proj_X(𝒜)`, `Q = Proj_X(ℬ)`, the open `U(ψ) ⊆ Q` and `r_ψ : U(ψ) ⟶ P`, the glued maps
`θ_d : r_ψ^*𝒪_P(d) ⟶ 𝒪_Q(d)|_{U(ψ)}` carry the inverse image along `r_ψ` of the multiplication
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of Stacks 084D to the inverse image along `U(ψ) ⟶ Q` of the
multiplication of the twists of `Q`, both read through Stacks 03EL.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.mul_comp_of_isDescendedChartHom`: glued maps
  between inverse images of descended modules carry descended multiplications to descended
  multiplications once their chart maps do.
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

attribute [local irreducible] CategoryTheory.yoneda

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

namespace RelativeProjHomPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  {M₁i M₁j M₁k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ₁i : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁i ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁i)
  (τ₁j : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁j ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁j)
  (τ₁k : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁k ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁k)
  (m₁ : quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) M₁i M₁j ⟶ M₁k)
  (hc₁i : PresentationSchemeCocycle (dP.spacePresentation Px hP) M₁i τ₁i)
  (hu₁i : PresentationSchemeUnit (dP.spacePresentation Px hP) M₁i τ₁i)
  (hc₁j : PresentationSchemeCocycle (dP.spacePresentation Px hP) M₁j τ₁j)
  (hu₁j : PresentationSchemeUnit (dP.spacePresentation Px hP) M₁j τ₁j)
  (hc₁k : PresentationSchemeCocycle (dP.spacePresentation Px hP) M₁k τ₁k)
  (hu₁k : PresentationSchemeUnit (dP.spacePresentation Px hP) M₁k τ₁k)
  (hbt₁ : RepresentedC3TensorCompat B S hS (dP.spaceTarget Px hP) M₁i M₁j)
  (hbs₁ : RepresentedC3TensorCompat B S hS (dP.spaceSource Px hP) M₁i M₁j)
  (hm₁ : dP.TransitionMulCompat Px hP τ₁i τ₁j τ₁k m₁)
  {M₂i M₂j M₂k : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ₂i : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂i ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂i)
  (τ₂j : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂j ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂j)
  (τ₂k : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂k ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂k)
  (m₂ : quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) M₂i M₂j ⟶ M₂k)
  (hc₂i : PresentationSchemeCocycle (dQ.spacePresentation Px hQ) M₂i τ₂i)
  (hu₂i : PresentationSchemeUnit (dQ.spacePresentation Px hQ) M₂i τ₂i)
  (hc₂j : PresentationSchemeCocycle (dQ.spacePresentation Px hQ) M₂j τ₂j)
  (hu₂j : PresentationSchemeUnit (dQ.spacePresentation Px hQ) M₂j τ₂j)
  (hc₂k : PresentationSchemeCocycle (dQ.spacePresentation Px hQ) M₂k τ₂k)
  (hu₂k : PresentationSchemeUnit (dQ.spacePresentation Px hQ) M₂k τ₂k)
  (hbt₂ : RepresentedC3TensorCompat B S hS (dQ.spaceTarget Px hQ) M₂i M₂j)
  (hbs₂ : RepresentedC3TensorCompat B S hS (dQ.spaceSource Px hQ) M₂i M₂j)
  (hm₂ : dQ.TransitionMulCompat Px hQ τ₂i τ₂j τ₂k m₂)
  (θUi : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁i ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂i)
  (θUj : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁j ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂j)
  (θUk : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁k ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂k)

section ChartMulOfHEq

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)

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

/-- A chart map `θ_n` built from modules equal to the inverse images of the twists of Tag 01NR,
through identifications which are identities, is the chart map with the identity
identifications. -/
theorem chartTwistMap_heq_chartTwistMapRefl (n : ℤ)
    (M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf).FullSubcategory)
    (eM₁ : M₁ = chartReflSourcePiece T f p hM₁ n)
    (c₁ : M₁.obj ≅ (Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n))
    (hc₁ : HEq c₁ (Iso.refl ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n))))
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf).FullSubcategory)
    (eM₂ : M₂ = chartReflTargetPiece T f q hM₂ n)
    (c₂ : M₂.obj ≅ (Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n))
    (hc₂ : HEq c₂ (Iso.refl ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))) :
    HEq (hψ.chartTwistMap T f n (M₁ := M₁) p hp c₁ (M₂ := M₂) q hq c₂)
      (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ n) := by
  subst eM₁ eM₂
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₂
  exact HEq.rfl

/-- **The chart maps `θ_n` carry the pulled-back multiplications to one another**, for families
of modules `M_n` equal to the twists of `P ×_X T` and `Q ×_X T`, chart maps equal to those with
the identity identifications, and multiplications `m₁`, `m₂` equal to the multiplications of the
twists of Tag 01NR. -/
theorem chartTwistMap_mul_of_heq
    (M₁ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf).FullSubcategory)
    (eM₁ : M₁ = chartReflSourcePiece T f p hM₁)
    (M₂ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf).FullSubcategory)
    (eM₂ : M₂ = chartReflTargetPiece T f q hM₂)
    (θ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (hψ.chartMapHom T f) (M₁ n) ⟶
      quasicoherentPullbackObj B S hS (hψ.chartIncl T f) (M₂ n))
    (eθ : ∀ n : ℤ, HEq (θ n) (hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ n)) (i j : ℤ)
    (m₁ : quasicoherentTensorObj B S hS (dP.fibre T f) (M₁ i) (M₁ j) ⟶ M₁ (i + j))
    (em₁ : HEq m₁ (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (pbAlgS p (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f))) i j) :
      quasicoherentTensorObj B S hS (dP.fibre T f) (chartReflSourcePiece T f p hM₁ i)
        (chartReflSourcePiece T f p hM₁ j) ⟶ chartReflSourcePiece T f p hM₁ (i + j)))
    (m₂ : quasicoherentTensorObj B S hS (dQ.fibre T f) (M₂ i) (M₂ j) ⟶ M₂ (i + j))
    (em₂ : HEq m₂ (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (pbAlgS q (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f))) i j) :
      quasicoherentTensorObj B S hS (dQ.fibre T f) (chartReflTargetPiece T f q hM₂ i)
        (chartReflTargetPiece T f q hM₂ j) ⟶ chartReflTargetPiece T f q hM₂ (i + j))) :
    quasicoherentTensorHom B S hS (hψ.chartObj T f) (θ i) (θ j) ≫
        (quasicoherentPullbackTensorIso B S hS (hψ.chartIncl T f) (M₂ i) (M₂ j)).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartIncl T f) m₂ =
      ((quasicoherentPullbackTensorIso B S hS (hψ.chartMapHom T f) (M₁ i) (M₁ j)).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartMapHom T f) m₁) ≫ θ (i + j) := by
  subst eM₁ eM₂
  obtain rfl : θ = hψ.chartTwistMapRefl T f p hp q hq hM₁ hM₂ :=
    funext fun n => eq_of_heq (eθ n)
  exact hψ.chartTwistMapRefl_mul T f p hp q hq hM₁ hM₂ i j m₁ (eq_of_heq em₁) m₂ (eq_of_heq em₂)

end ChartMulOfHEq

/-- **Glued morphisms `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` between inverse images of descended modules carry
descended multiplications to descended multiplications once their chart maps do**: for modules
descended from `(M, τ)` along the presentations of `P` and `Q`, with multiplications descended
from `m₁`, `m₂` (Stacks 03M3), morphisms `χ` which are `θ_U` on the chart `U(ψ)_U` carry
`r_ψ^*μ₁` to `ι^*μ₂`, read through Stacks 03EL, as soon as the `θ_U` carry the pulled-back `m₁` to
the pulled-back `m₂`. -/
theorem mul_comp_of_isDescendedChartHom
    (χi : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) M₁i τ₁i hc₁i hu₁i).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂i τ₂i hc₂i hu₂i).obj)
    (χj : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) M₁j τ₁j hc₁j hu₁j).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂j τ₂j hc₂j hu₂j).obj)
    (χk : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) M₁k τ₁k hc₁k hu₁k).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂k τ₂k hc₂k hu₂k).obj)
    (hχi : hψ.IsDescendedChartHom Px hG hP hQ M₁i τ₁i hc₁i hu₁i M₂i τ₂i hc₂i hu₂i θUi χi)
    (hχj : hψ.IsDescendedChartHom Px hG hP hQ M₁j τ₁j hc₁j hu₁j M₂j τ₂j hc₂j hu₂j θUj χj)
    (hχk : hψ.IsDescendedChartHom Px hG hP hQ M₁k τ₁k hc₁k hu₁k M₂k τ₂k hc₂k hu₂k θUk χk)
    (hθU : quasicoherentTensorHom B S hS (hψ.chartObj Px.U Px.toSpace) θUi θUj ≫
        (quasicoherentPullbackTensorIso B S hS (hψ.chartIncl Px.U Px.toSpace) M₂i M₂j).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartIncl Px.U Px.toSpace) m₂ =
      ((quasicoherentPullbackTensorIso B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁i M₁j).inv ≫
        quasicoherentPullbackMap B S hS (hψ.chartMapHom Px.U Px.toSpace) m₁) ≫ θUk) :
    (modulePullbackTensorIso B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
        (presentationDescendedModule (dP.spacePresentation Px hP) M₁i τ₁i hc₁i hu₁i).obj
        (presentationDescendedModule (dP.spacePresentation Px hP) M₁j τ₁j hc₁j hu₁j).obj).inv ≫
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).map
        (dP.spacePresentationDescendedMul Px hP τ₁i τ₁j τ₁k m₁ hc₁i hu₁i hc₁j hu₁j hc₁k hu₁k
          hbt₁ hbs₁ hm₁) ≫ χk =
    (χi ⊗ₘ χj) ≫
      (modulePullbackTensorIso B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
        (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂i τ₂i hc₂i hu₂i).obj
        (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂j τ₂j hc₂j hu₂j).obj).inv ≫
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).map
        (dQ.spacePresentationDescendedMul Px hQ τ₂i τ₂j τ₂k m₂ hc₂i hu₂i hc₂j hu₂j hc₂k hu₂k
          hbt₂ hbs₂ hm₂) := by
  have hμ₁ : ChartMulReading (presentationAtlas (dP.spacePresentation Px hP))
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS
        (dP.fibre Px.U Px.toSpace)).functor.obj M₁i).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS
        (dP.fibre Px.U Px.toSpace)).functor.obj M₁j).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS
        (dP.fibre Px.U Px.toSpace)).functor.obj M₁k).obj)
      (dP.spacePresentationDescendedMul Px hP τ₁i τ₁j τ₁k m₁ hc₁i hu₁i hc₁j hu₁j hc₁k hu₁k
        hbt₁ hbs₁ hm₁)
      (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁i τ₁i hc₁i hu₁i).hom
      (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁j τ₁j hc₁j hu₁j).hom
      (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁k τ₁k hc₁k hu₁k).hom
      (representedTensorChartMul B S hS m₁) :=
    dP.chartMulReading_spacePresentationDescendedMul Px hP τ₁i τ₁j τ₁k m₁ hc₁i hu₁i hc₁j hu₁j
      hc₁k hu₁k hbt₁ hbs₁ hm₁
  have hμ₂ : ChartMulReading (presentationAtlas (dQ.spacePresentation Px hQ))
      (Li := ((representedQuasicoherentSchemeEquivalence B S hS
        (dQ.fibre Px.U Px.toSpace)).functor.obj M₂i).obj)
      (Lj := ((representedQuasicoherentSchemeEquivalence B S hS
        (dQ.fibre Px.U Px.toSpace)).functor.obj M₂j).obj)
      (Lk := ((representedQuasicoherentSchemeEquivalence B S hS
        (dQ.fibre Px.U Px.toSpace)).functor.obj M₂k).obj)
      (dQ.spacePresentationDescendedMul Px hQ τ₂i τ₂j τ₂k m₂ hc₂i hu₂i hc₂j hu₂j hc₂k hu₂k
        hbt₂ hbs₂ hm₂)
      (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂i τ₂i hc₂i hu₂i).hom
      (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂j τ₂j hc₂j hu₂j).hom
      (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂k τ₂k hc₂k hu₂k).hom
      (representedTensorChartMul B S hS m₂) :=
    dQ.chartMulReading_spacePresentationDescendedMul Px hQ τ₂i τ₂j τ₂k m₂ hc₂i hu₂i hc₂j hu₂j
      hc₂k hu₂k hbt₂ hbs₂ hm₂
  exact hψ.mul_comp_of_isChartHom Px hG hP hQ
    (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁i τ₁i hc₁i hu₁i)
    (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁j τ₁j hc₁j hu₁j)
    (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁k τ₁k hc₁k hu₁k)
    (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂i τ₂i hc₂i hu₂i)
    (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂j τ₂j hc₂j hu₂j)
    (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂k τ₂k hc₂k hu₂k)
    θUi θUj θUk χi χj χk hχi hχj hχk _ m₁ hμ₁ _ m₂ hμ₂ hθU


/-- **Glued morphisms between inverse images of descended twists carry descended multiplications
to descended multiplications**: `mul_comp_of_isDescendedChartHom` for families of modules `N_n`
equal to the twists of `P ×_X U` and `Q ×_X U`, chart maps `θ_n` equal to those with the identity
identifications and multiplications `m₁`, `m₂` equal to the multiplications of the twists of
Tag 01NR, so that the chart maps carry `m₁` to `m₂` by `chartTwistMap_mul_of_heq`. -/
theorem mul_comp_of_isDescendedChartHom_of_heq
    (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre Px.U Px.toSpace) ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (dP.algebra Px.U Px.toSpace)).scheme)
    (hp : p = (dP.fibreIso Px.U Px.toSpace).hom)
    (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre Px.U Px.toSpace) ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (dQ.algebra Px.U Px.toSpace)).scheme)
    (hq : q = (dQ.fibreIso Px.U Px.toSpace).hom)
    (hM₁ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (dP.fibre Px.U Px.toSpace)).ringCatSheaf
      ((Scheme.Modules.pullback p).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra Px.U Px.toSpace)).piece
          n)))
    (hM₂ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (dQ.fibre Px.U Px.toSpace)).ringCatSheaf
      ((Scheme.Modules.pullback q).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra Px.U Px.toSpace)).piece
          n)))
    (N₁ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (eN₁ : N₁ = chartReflSourcePiece Px.U Px.toSpace p hM₁)
    (N₂ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (eN₂ : N₂ = chartReflTargetPiece Px.U Px.toSpace q hM₂)
    (θ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) (N₁ n) ⟶
      quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) (N₂ n))
    (eθ : ∀ n : ℤ, HEq (θ n) (hψ.chartTwistMapRefl Px.U Px.toSpace p hp q hq hM₁ hM₂ n))
    (τ₁ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) (N₁ n) ⟶
      quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) (N₁ n))
    (hτ₁ : ∀ n : ℤ, PresentationSchemeCocycle (dP.spacePresentation Px hP) (N₁ n) (τ₁ n))
    (hυ₁ : ∀ n : ℤ, PresentationSchemeUnit (dP.spacePresentation Px hP) (N₁ n) (τ₁ n))
    (τ₂ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) (N₂ n) ⟶
      quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) (N₂ n))
    (hτ₂ : ∀ n : ℤ, PresentationSchemeCocycle (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n))
    (hυ₂ : ∀ n : ℤ, PresentationSchemeUnit (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n))
    (χ : ∀ n : ℤ, (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) (N₁ n) (τ₁ n) (hτ₁ n)
            (hυ₁ n)).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n) (hτ₂ n)
            (hυ₂ n)).obj)
    (hχ : ∀ n : ℤ, hψ.IsDescendedChartHom Px hG hP hQ (N₁ n) (τ₁ n) (hτ₁ n) (hυ₁ n) (N₂ n)
      (τ₂ n) (hτ₂ n) (hυ₂ n) (θ n) (χ n))
    (i j : ℤ)
    (mm₁ : quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) (N₁ i) (N₁ j) ⟶ N₁ (i + j))
    (em₁ : HEq mm₁ (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS p
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra Px.U Px.toSpace))) i j) :
      quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace)
        (chartReflSourcePiece Px.U Px.toSpace p hM₁ i)
        (chartReflSourcePiece Px.U Px.toSpace p hM₁ j) ⟶
        chartReflSourcePiece Px.U Px.toSpace p hM₁ (i + j)))
    (hb₁t : RepresentedC3TensorCompat B S hS (dP.spaceTarget Px hP) (N₁ i) (N₁ j))
    (hb₁s : RepresentedC3TensorCompat B S hS (dP.spaceSource Px hP) (N₁ i) (N₁ j))
    (hmc₁ : dP.TransitionMulCompat Px hP (τ₁ i) (τ₁ j) (τ₁ (i + j)) mm₁)
    (mm₂ : quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) (N₂ i) (N₂ j) ⟶ N₂ (i + j))
    (em₂ : HEq mm₂ (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS q
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra Px.U Px.toSpace))) i j) :
      quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace)
        (chartReflTargetPiece Px.U Px.toSpace q hM₂ i)
        (chartReflTargetPiece Px.U Px.toSpace q hM₂ j) ⟶
        chartReflTargetPiece Px.U Px.toSpace q hM₂ (i + j)))
    (hb₂t : RepresentedC3TensorCompat B S hS (dQ.spaceTarget Px hQ) (N₂ i) (N₂ j))
    (hb₂s : RepresentedC3TensorCompat B S hS (dQ.spaceSource Px hQ) (N₂ i) (N₂ j))
    (hmc₂ : dQ.TransitionMulCompat Px hQ (τ₂ i) (τ₂ j) (τ₂ (i + j)) mm₂) :
    (modulePullbackTensorIso B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
        (presentationDescendedModule (dP.spacePresentation Px hP) (N₁ i) (τ₁ i) (hτ₁ i)
          (hυ₁ i)).obj
        (presentationDescendedModule (dP.spacePresentation Px hP) (N₁ j) (τ₁ j) (hτ₁ j)
          (hυ₁ j)).obj).inv ≫
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).map
        (dP.spacePresentationDescendedMul Px hP (τ₁ i) (τ₁ j) (τ₁ (i + j)) mm₁ (hτ₁ i) (hυ₁ i)
          (hτ₁ j) (hυ₁ j) (hτ₁ (i + j)) (hυ₁ (i + j)) hb₁t hb₁s hmc₁) ≫ χ (i + j) =
    (χ i ⊗ₘ χ j) ≫
      (modulePullbackTensorIso B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
        (presentationDescendedModule (dQ.spacePresentation Px hQ) (N₂ i) (τ₂ i) (hτ₂ i)
          (hυ₂ i)).obj
        (presentationDescendedModule (dQ.spacePresentation Px hQ) (N₂ j) (τ₂ j) (hτ₂ j)
          (hυ₂ j)).obj).inv ≫
      (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).map
        (dQ.spacePresentationDescendedMul Px hQ (τ₂ i) (τ₂ j) (τ₂ (i + j)) mm₂ (hτ₂ i) (hυ₂ i)
          (hτ₂ j) (hυ₂ j) (hτ₂ (i + j)) (hυ₂ (i + j)) hb₂t hb₂s hmc₂) :=
  hψ.mul_comp_of_isDescendedChartHom Px hG hP hQ (τ₁ i) (τ₁ j) (τ₁ (i + j)) mm₁ (hτ₁ i) (hυ₁ i)
    (hτ₁ j) (hυ₁ j) (hτ₁ (i + j)) (hυ₁ (i + j)) hb₁t hb₁s hmc₁ (τ₂ i) (τ₂ j) (τ₂ (i + j)) mm₂
    (hτ₂ i) (hυ₂ i) (hτ₂ j) (hυ₂ j) (hτ₂ (i + j)) (hυ₂ (i + j)) hb₂t hb₂s hmc₂ (θ i) (θ j)
    (θ (i + j)) (χ i) (χ j) (χ (i + j)) (hχ i) (hχ j) (hχ (i + j))
    (hψ.chartTwistMap_mul_of_heq Px.U Px.toSpace p hp q hq hM₁ hM₂ N₁ eN₁ N₂ eN₂ θ eθ i j mm₁ em₁
      mm₂ em₂)

/-- **Glued morphisms between inverse images of descended twists carry descended multiplications
to descended multiplications, in all degrees**:
`AlgebraicGeometry.Space.RelativeProjHomPoints.mul_comp_of_isDescendedChartHom_of_heq` as
`AlgebraicGeometry.Space.PullMulCompat`. -/
theorem pullMulCompat_of_isDescendedChartHom_of_heq
    (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre Px.U Px.toSpace) ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (dP.algebra Px.U Px.toSpace)).scheme)
    (hp : p = (dP.fibreIso Px.U Px.toSpace).hom)
    (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre Px.U Px.toSpace) ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (dQ.algebra Px.U Px.toSpace)).scheme)
    (hq : q = (dQ.fibreIso Px.U Px.toSpace).hom)
    (hM₁ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (dP.fibre Px.U Px.toSpace)).ringCatSheaf
      ((Scheme.Modules.pullback p).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra Px.U Px.toSpace)).piece
          n)))
    (hM₂ : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (dQ.fibre Px.U Px.toSpace)).ringCatSheaf
      ((Scheme.Modules.pullback q).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra Px.U Px.toSpace)).piece
          n)))
    (N₁ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (eN₁ : N₁ = chartReflSourcePiece Px.U Px.toSpace p hM₁)
    (N₂ : ℤ → (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (eN₂ : N₂ = chartReflTargetPiece Px.U Px.toSpace q hM₂)
    (θ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) (N₁ n) ⟶
      quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) (N₂ n))
    (eθ : ∀ n : ℤ, HEq (θ n) (hψ.chartTwistMapRefl Px.U Px.toSpace p hp q hq hM₁ hM₂ n))
    (τ₁ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) (N₁ n) ⟶
      quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) (N₁ n))
    (hτ₁ : ∀ n : ℤ, PresentationSchemeCocycle (dP.spacePresentation Px hP) (N₁ n) (τ₁ n))
    (hυ₁ : ∀ n : ℤ, PresentationSchemeUnit (dP.spacePresentation Px hP) (N₁ n) (τ₁ n))
    (τ₂ : ∀ n : ℤ, quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) (N₂ n) ⟶
      quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) (N₂ n))
    (hτ₂ : ∀ n : ℤ, PresentationSchemeCocycle (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n))
    (hυ₂ : ∀ n : ℤ, PresentationSchemeUnit (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n))
    (χ : ∀ n : ℤ, (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) (N₁ n) (τ₁ n) (hτ₁ n)
            (hυ₁ n)).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n) (hτ₂ n)
            (hυ₂ n)).obj)
    (hχ : ∀ n : ℤ, hψ.IsDescendedChartHom Px hG hP hQ (N₁ n) (τ₁ n) (hτ₁ n) (hυ₁ n) (N₂ n)
      (τ₂ n) (hτ₂ n) (hυ₂ n) (θ n) (χ n))
    (mm₁ : ∀ i j : ℤ,
      quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace) (N₁ i) (N₁ j) ⟶ N₁ (i + j))
    (em₁ : ∀ i j : ℤ, HEq (mm₁ i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS p
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra Px.U Px.toSpace))) i j) :
      quasicoherentTensorObj B S hS (dP.fibre Px.U Px.toSpace)
        (chartReflSourcePiece Px.U Px.toSpace p hM₁ i)
        (chartReflSourcePiece Px.U Px.toSpace p hM₁ j) ⟶
        chartReflSourcePiece Px.U Px.toSpace p hM₁ (i + j)))
    (hb₁t : ∀ i j : ℤ, RepresentedC3TensorCompat B S hS (dP.spaceTarget Px hP) (N₁ i) (N₁ j))
    (hb₁s : ∀ i j : ℤ, RepresentedC3TensorCompat B S hS (dP.spaceSource Px hP) (N₁ i) (N₁ j))
    (hmc₁ : ∀ i j : ℤ, dP.TransitionMulCompat Px hP (τ₁ i) (τ₁ j) (τ₁ (i + j)) (mm₁ i j))
    (mm₂ : ∀ i j : ℤ,
      quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace) (N₂ i) (N₂ j) ⟶ N₂ (i + j))
    (em₂ : ∀ i j : ℤ, HEq (mm₂ i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS q
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra Px.U Px.toSpace))) i j) :
      quasicoherentTensorObj B S hS (dQ.fibre Px.U Px.toSpace)
        (chartReflTargetPiece Px.U Px.toSpace q hM₂ i)
        (chartReflTargetPiece Px.U Px.toSpace q hM₂ j) ⟶
        chartReflTargetPiece Px.U Px.toSpace q hM₂ (i + j)))
    (hb₂t : ∀ i j : ℤ, RepresentedC3TensorCompat B S hS (dQ.spaceTarget Px hQ) (N₂ i) (N₂ j))
    (hb₂s : ∀ i j : ℤ, RepresentedC3TensorCompat B S hS (dQ.spaceSource Px hQ) (N₂ i) (N₂ j))
    (hmc₂ : ∀ i j : ℤ, dQ.TransitionMulCompat Px hQ (τ₂ i) (τ₂ j) (τ₂ (i + j)) (mm₂ i j)) :
    PullMulCompat
      (ObjectProperty.homMk hψ.relativeMapSpaceHom :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
      (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
        (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
      (fun n => (presentationDescendedModule (dP.spacePresentation Px hP) (N₁ n) (τ₁ n) (hτ₁ n)
        (hυ₁ n)).obj)
      (fun n => (presentationDescendedModule (dQ.spacePresentation Px hQ) (N₂ n) (τ₂ n) (hτ₂ n)
        (hυ₂ n)).obj) χ
      (fun i j => dP.spacePresentationDescendedMul Px hP (τ₁ i) (τ₁ j) (τ₁ (i + j)) (mm₁ i j)
        (hτ₁ i) (hυ₁ i) (hτ₁ j) (hυ₁ j) (hτ₁ (i + j)) (hυ₁ (i + j)) (hb₁t i j) (hb₁s i j)
        (hmc₁ i j))
      (fun i j => dQ.spacePresentationDescendedMul Px hQ (τ₂ i) (τ₂ j) (τ₂ (i + j)) (mm₂ i j)
        (hτ₂ i) (hυ₂ i) (hτ₂ j) (hυ₂ j) (hτ₂ (i + j)) (hυ₂ (i + j)) (hb₂t i j) (hb₂s i j)
        (hmc₂ i j)) :=
  fun i j => hψ.mul_comp_of_isDescendedChartHom_of_heq Px hG hP hQ p hp q hq hM₁ hM₂ N₁ eN₁ N₂ eN₂
    θ eθ τ₁ hτ₁ hυ₁ τ₂ hτ₂ hυ₂ χ hχ i j (mm₁ i j) (em₁ i j) (hb₁t i j) (hb₁s i j) (hmc₁ i j)
    (mm₂ i j) (em₂ i j) (hb₂t i j) (hb₂s i j) (hmc₂ i j)

end RelativeProjHomPoints

namespace RelativeProjSituation

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

section Generic

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The twists on the scheme of `V ×_X P` are the inverse images of the twists of Tag 01NR along
`AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`, spelled through the algebra of the
scheme points of `P`. -/
theorem twistPieceQcoh_eq_chartReflSourcePiece (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    s.twistPieceQcoh V v = RelativeProjHomPoints.chartReflSourcePiece (dP := s.relativeProjPoints)
      V v (s.toRelativeProj V v) (fun n => (s.twistPieceQcoh V v n).2) :=
  rfl

/-- The identification of the twists with the inverse images of the twists of Tag 01NR is the
identity. -/
theorem twistPieceQcohObjIso_heq_refl (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℤ) :
    HEq (s.twistPieceQcohObjIso V v n)
      (Iso.refl ((Scheme.Modules.pullback (s.toRelativeProj V v)).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
          (s.relativeProjPoints.algebra V v)).piece n))) :=
  HEq.rfl

/-- The multiplication of the twists on the scheme of `V ×_X P` is the multiplication of the
inverse image of Tag 01NR's `⨁_n 𝒪(n)`, spelled through the algebra of the scheme points of `P`. -/
theorem twistPieceMul_heq_homMk (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (i j : ℤ) :
    HEq (s.twistPieceMul V v i j) (ObjectProperty.homMk (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS (s.toRelativeProj V v)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.relativeProjPoints.algebra V v)))
        i j) :
      quasicoherentTensorObj s.site s.base s.containsBase (s.relativeProjPoints.fibre V v)
        (RelativeProjHomPoints.chartReflSourcePiece (dP := s.relativeProjPoints) V v
          (s.toRelativeProj V v) (fun n => (s.twistPieceQcoh V v n).2) i)
        (RelativeProjHomPoints.chartReflSourcePiece (dP := s.relativeProjPoints) V v
          (s.toRelativeProj V v) (fun n => (s.twistPieceQcoh V v n).2) j) ⟶
        RelativeProjHomPoints.chartReflSourcePiece (dP := s.relativeProjPoints) V v
          (s.toRelativeProj V v) (fun n => (s.twistPieceQcoh V v n).2) (i + j)) :=
  HEq.rfl

end Generic

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

/-- The chart map `θ_n` of Tag 07ZG on `U(ψ) ×_X U` is the chart map with the identity
identifications of the twists. -/
theorem twistChartMap_heq_chartTwistMapRefl (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ X.1)
    (n : ℤ) :
    type_of% ((𝔥).chartTwistMap_heq_chartTwistMapRefl U u ((𝔰₁).toRelativeProj U u)
      ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u) ((𝔰₂).toRelativeProj U u)
      ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u) (fun n => ((𝔰₁).twistPieceQcoh U u n).2)
      (fun n => ((𝔰₂).twistPieceQcoh U u n).2) n ((𝔰₁).twistPieceQcoh U u n)
      (congrFun ((𝔰₁).twistPieceQcoh_eq_chartReflSourcePiece U u) n)
      ((𝔰₁).twistPieceQcohObjIso U u n) ((𝔰₁).twistPieceQcohObjIso_heq_refl U u n)
      ((𝔰₂).twistPieceQcoh U u n) (congrFun ((𝔰₂).twistPieceQcoh_eq_chartReflSourcePiece U u) n)
      ((𝔰₂).twistPieceQcohObjIso U u n) ((𝔰₂).twistPieceQcohObjIso_heq_refl U u n)) :=
  (𝔥).chartTwistMap_heq_chartTwistMapRefl U u _ ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u) _
    ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u) _ _ n _
    (congrFun ((𝔰₁).twistPieceQcoh_eq_chartReflSourcePiece U u) n) _
    ((𝔰₁).twistPieceQcohObjIso_heq_refl U u n) _
    (congrFun ((𝔰₂).twistPieceQcoh_eq_chartReflSourcePiece U u) n) _
    ((𝔰₂).twistPieceQcohObjIso_heq_refl U u n)

/-- **The chart maps `θ_n` of Tag 07ZG carry the multiplication of the twists of `P ×_X U` to
that of `Q ×_X U`**, on the chart `U(ψ) ×_X U`, with the twists spelled as on the presentation. -/
theorem twistChartMap_mul_twistPieceMul (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ X.1)
    (i j : ℤ) :
    type_of% ((𝔥).chartTwistMap_mul_of_heq U u ((𝔰₁).toRelativeProj U u)
      ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u) ((𝔰₂).toRelativeProj U u)
      ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u) (fun n => ((𝔰₁).twistPieceQcoh U u n).2)
      (fun n => ((𝔰₂).twistPieceQcoh U u n).2) ((𝔰₁).twistPieceQcoh U u)
      ((𝔰₁).twistPieceQcoh_eq_chartReflSourcePiece U u) ((𝔰₂).twistPieceQcoh U u)
      ((𝔰₂).twistPieceQcoh_eq_chartReflSourcePiece U u)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ U u)
      (twistChartMap_heq_chartTwistMapRefl h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ U u) i j
      ((𝔰₁).twistPieceMul U u i j) ((𝔰₁).twistPieceMul_heq_homMk U u i j)
      ((𝔰₂).twistPieceMul U u i j) ((𝔰₂).twistPieceMul_heq_homMk U u i j)) :=
  (𝔥).chartTwistMap_mul_of_heq U u ((𝔰₁).toRelativeProj U u)
    ((𝔰₁).toRelativeProj_eq_fibreIso_hom U u) ((𝔰₂).toRelativeProj U u)
    ((𝔰₂).toRelativeProj_eq_fibreIso_hom U u) (fun n => ((𝔰₁).twistPieceQcoh U u n).2)
    (fun n => ((𝔰₂).twistPieceQcoh U u n).2) ((𝔰₁).twistPieceQcoh U u)
    ((𝔰₁).twistPieceQcoh_eq_chartReflSourcePiece U u) ((𝔰₂).twistPieceQcoh U u)
    ((𝔰₂).twistPieceQcoh_eq_chartReflSourcePiece U u)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ U u)
    (twistChartMap_heq_chartTwistMapRefl h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ U u) i j
    ((𝔰₁).twistPieceMul U u i j) ((𝔰₁).twistPieceMul_heq_homMk U u i j)
    ((𝔰₂).twistPieceMul U u i j) ((𝔰₂).twistPieceMul_heq_homMk U u i j)

/-- **The maps `θ_d : r_ψ^*𝒪_P(d) ⟶ ι^*𝒪_Q(d)` of Stacks 085F carry multiplications to
multiplications**: the inverse image along `r_ψ` of the multiplication
`𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` followed by `θ_{i+j}` is `θ_i ⊗ θ_j` followed by the inverse image
along `ι : U(ψ) ⟶ Q` of the multiplication of the twists of `Q`, both read through Stacks 03EL. -/
theorem twistMap_mul :
    PullMulCompat (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (fun n => ((𝔰₁).twistModule Px n).obj) (fun n => ((𝔰₂).twistModule Px n).obj)
      (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
      (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j) :=
  (𝔥).pullMulCompat_of_isDescendedChartHom_of_heq Px (𝒢).2
    (𝔰₁).isAlgebraicSpace_relativeProjFunctor (𝔰₂).isAlgebraicSpace_relativeProjFunctor
    ((𝔰₁).toRelativeProj Px.U Px.toSpace) ((𝔰₁).toRelativeProj_eq_fibreIso_hom Px.U Px.toSpace)
    ((𝔰₂).toRelativeProj Px.U Px.toSpace) ((𝔰₂).toRelativeProj_eq_fibreIso_hom Px.U Px.toSpace)
    (fun n => ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n).2)
    (fun n => ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n).2)
    ((𝔰₁).twistPieceQcoh Px.U Px.toSpace)
    ((𝔰₁).twistPieceQcoh_eq_chartReflSourcePiece Px.U Px.toSpace)
    ((𝔰₂).twistPieceQcoh Px.U Px.toSpace)
    ((𝔰₂).twistPieceQcoh_eq_chartReflSourcePiece Px.U Px.toSpace)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace)
    (twistChartMap_heq_chartTwistMapRefl h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace)
    ((𝔰₁).twistTransition Px) ((𝔰₁).presentationSchemeCocycle_twistTransition Px)
    ((𝔰₁).presentationSchemeUnit_twistTransition Px)
    ((𝔰₂).twistTransition Px) ((𝔰₂).presentationSchemeCocycle_twistTransition Px)
    ((𝔰₂).presentationSchemeUnit_twistTransition Px)
    (twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px)
    (isDescendedChartHom_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px)
    ((𝔰₁).twistPieceMul Px.U Px.toSpace) ((𝔰₁).twistPieceMul_heq_homMk Px.U Px.toSpace)
    (fun _ _ => representedC3TensorCompat B S hS _ _ _)
    (fun _ _ => representedC3TensorCompat B S hS _ _ _)
    ((𝔰₁).transitionMulCompat_twistTransition Px)
    ((𝔰₂).twistPieceMul Px.U Px.toSpace) ((𝔰₂).twistPieceMul_heq_homMk Px.U Px.toSpace)
    (fun _ _ => representedC3TensorCompat B S hS _ _ _)
    (fun _ _ => representedC3TensorCompat B S hS _ _ _)
    ((𝔰₂).transitionMulCompat_twistTransition Px)

/-- **Stacks 085F, the map `θ` of `ℤ`-graded `𝒪_{U(ψ)}`-algebras**
`θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_P(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_Q(d)|_{U(ψ)}`, between the inverse images (Stacks 0FQX)
along `r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q` of the graded algebras of twists of Stacks 084D; its
degree-`d` component is the glued map `θ_d`. -/
def twistAlgebraHom :
    SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₁ h₁c h₁n h₁q h₁k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₁).twistGradedAlgebra Px))
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₂ h₂c h₂n h₂q h₂k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₂).twistGradedAlgebra Px)) :=
  twistAlgebraHomOfMul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
    (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px)

/-- The degree-`d` component of `θ` is the glued map `θ_d`. -/
theorem twistAlgebraHom_app (n : ℤ) :
    gradedPullHomApp (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
        (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) ((𝔰₁).twistGradedAlgebra Px)
        ((𝔰₂).twistGradedAlgebra Px) (twistAlgebraHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) n =
      twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n :=
  twistAlgebraHomOfMul_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
    (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) n

end Map

end RelativeProjSituation

end AlgebraicGeometry.Space

end
