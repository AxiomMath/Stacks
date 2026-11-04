module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentInto

/-!
# The homomorphism `ψ : π^*𝒜 ⟶ ⨁ 𝒪_P(n)` of Stacks 084D on the atlas

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of
Stacks 084B and `X = U/R` a presentation of its base, so that `P = P_U/P_R` with
`P_U = U ×_X P`.  The twists `𝒪_P(n)` are descended from the twists `𝒪(n)` of Stacks 01NR on the
scheme of `P_U` (`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`).  This file builds
the source of the homomorphism `ψ` of Stacks 084D on the atlas `c : P_U ⟶ P`: the inverse image
`c^*(π^*𝒜_n)` is identified with the module attached by Stacks 03DX (2) to the pullback
`π_U^*(u^*𝒜)_n` of the restriction of `𝒜` to the scheme point `u : U ⟶ X`, and the
homomorphism-of-sections map `ψ` of Stacks 01NR at that point, in its adjoint form
`π_U^*(u^*𝒜)_n ⟶ 𝒪(n)`, is carried to a morphism `c^*(π^*𝒜_n) ⟶ c^*𝒪_P(n)` on the atlas.

The identification is the composite of the composition comparisons of Stacks 03LU along
`c ≫ π = π_U ≫ u`, the identification of the quasi-coherent `𝒪`-module `u^*𝒜_n` on the represented
algebraic space `U` with the module attached to its Zariski reading
(`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`), and the identification of inverse
images of attached modules along `π_U`
(`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjSpaceHom`: `π : P ⟶ X` as a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiSourceQcoh`: the source `π^*𝒜_n` of `ψ` in
  degree `n`, as a quasi-coherent `𝒪_P`-module.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`: **`c^*(π^*𝒜_n)` is the module
  attached to `π_U^*(u^*𝒜)_n`.**
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHom`: the adjoint form
  `π_U^*(u^*𝒜)_n ⟶ 𝒪(n)` of Tag 01NR's `ψ` on the scheme of `P_U`.
* `AlgebraicGeometry.Space.RelativeProjSituation.psiChartHom`: **`ψ` on the atlas**, the morphism
  `c^*(π^*𝒜_n) ⟶ 𝒪(n)^a` to be descended to `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-- The Zariski reading `(u^*𝒜)_n` of the restriction of a quasi-coherent graded algebra `𝒜` on
`X` to the atlas `u : U ⟶ X` of a presentation, as a quasi-coherent module on the scheme of
`U`. -/
abbrev presentationPointPieceQcoh {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (Px : Presentation B S hS X.obj X.property)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite) (n : ℤ) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Px.U).ringCatSheaf).FullSubcategory :=
  zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
    (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)

/-- **The atlas of the presentation of `P`, followed by `π`, is the structure morphism of
`P_U = U ×_X P` followed by the atlas of `X`**, as morphisms of algebraic spaces. -/
theorem presentationAtlas_comp_homMk :
    presentationAtlas (d.spacePresentation Px hP) ≫
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
      representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace) ≫ pointHom Px.toSpace :=
  ObjectProperty.hom_ext _ (d.isPullback Px.U Px.toSpace).w

section ChartSource

attribute [local irreducible] CategoryTheory.yoneda

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- **The inverse image of `π^*𝒜_n` along the atlas `c : P_U ⟶ P` of the presentation of `P` is
the module attached by Stacks 03DX (2) to `π_U^*(u^*𝒜)_n`**, for `π_U : P_U ⟶ U` the structure
morphism of the base change and `u : U ⟶ X` the atlas of the base.  It is the composition
comparison of Stacks 03LU along `c ≫ π = π_U ≫ u`, the identification of `u^*𝒜_n` with the module
attached to its Zariski reading (`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`), and the
identification of the inverse image along `π_U` of an attached module
(`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`). -/
def chartPullbackIso (n : ℤ) :
    (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj
        ((modulePullback B S hS
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
          (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace)
            (presentationPointPieceQcoh Px A hA n))).obj :=
  (modulePullbackCompIso B S hS (presentationAtlas (d.spacePresentation Px hP))
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).app (A.piece n) ≪≫
    eqToIso (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n))
      (d.presentationAtlas_comp_homMk Px hP)) ≪≫
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
        (pointHom Px.toSpace)).app (A.piece n)).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).mapIso
      (zariskiReadingQuasicoherentIso Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) ≪≫
    modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom Px.U Px.toSpace)
      (presentationPointPieceQcoh Px A hA n)

end ChartSource

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The structure morphism `π : P ⟶ X` of the relative Proj of Situation 0849, as a morphism of
algebraic spaces. -/
abbrev relativeProjSpaceHom :
    (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space :=
  ObjectProperty.homMk s.relativeProjπ

/-- **The source `π^*𝒜_n` of `ψ` in degree `n`**, as a quasi-coherent `𝒪_P`-module. -/
abbrev psiSourceQcoh (n : ℤ) :
    QuasicoherentSheaves.{u, u} s.site s.base s.containsBase s.relativeProjFunctor
      s.isAlgebraicSpace_relativeProjFunctor :=
  ⟨(modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
      (s.shrink.algebra.piece n),
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase
      s.relativeProjSpaceHom _ (s.shrink.isQuasicoherent n)⟩

/-- **The inverse image of `π^*𝒜_n` along the atlas `c : P_U ⟶ P` is the module attached by
Stacks 03DX (2) to `π_U^*(u^*𝒜)_n`** (`…RelativeProjPoints.chartPullbackIso` in Situation 0849). -/
def psiChartSourceIso (n : ℤ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).obj
        (s.psiSourceQcoh n).obj ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
            (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent n))).obj :=
  s.relativeProjPoints.chartPullbackIso Px s.isAlgebraicSpace_relativeProjFunctor
    s.shrink.algebra s.shrink.isQuasicoherent n

/-- The structure morphism of `U ×_X P` is, on schemes, the structure morphism of the relative
homogeneous spectrum `Proj_U(u^*𝒜)` read through
`AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
theorem toScheme_map_fibreHom (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map (s.relativeProjPoints.fibreHom V v) =
      s.toRelativeProj V v ≫ (relativeProj (s.shrink.pointAlgebra V v)).toBase :=
  s.relativeProjPoints.fibreHom_comp V v

/-- **Tag 01NR's `ψ` on the scheme of `V ×_X P`, in adjoint form**: the transpose
`π_V^*(v^*𝒜)_n ⟶ 𝒪(n)` of the homogeneous-section map `(v^*𝒜)_n ⟶ π_{V*}𝒪(n)`, read on the
scheme of `V ×_X P`, with `π_V` the structure morphism `V ×_X P ⟶ V`. -/
def psiChartSchemeHom (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℕ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.fibreHom V v))).obj ((s.shrink.pointAlgebra V v).piece (n : ℤ)) ⟶
      (s.twistPieceQcoh V v (n : ℤ)).obj :=
  (Scheme.Modules.pullbackCongr (s.toScheme_map_fibreHom V v)).hom.app _ ≫
    (Scheme.Modules.pullbackComp (s.toRelativeProj V v)
      (relativeProj (s.shrink.pointAlgebra V v)).toBase).inv.app _ ≫
    (Scheme.Modules.pullback (s.toRelativeProj V v)).map
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (relativeProj (s.shrink.pointAlgebra V v)).toBase).homEquiv _ _).symm
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra (s.shrink.pointAlgebra V v)).ψ n))

/-- **`ψ` on the atlas in degree `n`**: the morphism `c^*(π^*𝒜_n) ⟶ 𝒪(n)^a` from the inverse image
of the source of `ψ` along the atlas `c : P_U ⟶ P` to the module attached to the twist `𝒪(n)` of
Tag 01NR on the scheme of `P_U`: the identification
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso` followed by the module attached
to Tag 01NR's `ψ` in adjoint form. -/
def psiChartHom (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).obj
        (s.psiSourceQcoh (n : ℤ)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
          (s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))).obj :=
  (s.psiChartSourceIso Px (n : ℤ)).hom ≫
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.map
        (ObjectProperty.homMk (s.psiChartSchemeHom Px.U Px.toSpace n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (n : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))).hom

end RelativeProjSituation

end AlgebraicGeometry.Space

end
