module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPsi
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelDictionary

/-!
# The chart dictionary of Stacks 085L at the atlas

Let `P = Proj_X(𝒜)` with `π : P ⟶ X`, let `i : Z ⟶ P` be a closed immersion and let
`ψ : π^*𝒜_n ⟶ 𝒪_P(n)` be the map of Stacks 084D, characterised by its inverse image along the
atlas `P_U ⟶ P` over an atlas `u : U ⟶ X`.  At a Zariski open `W` of `U`, a local section `a` of
`(u^*𝒜)_n` lies in the graded ideal of Stacks 0801 of the closed subscheme `Z ×_X U` of
`Proj_U(u^*𝒜)` exactly when the canonical map `𝒜_n ⟶ π_*i_*i^*𝒪_P(n)` kills the reading of `a` on
the étale chart `W ⟶ U ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.C1359Bridge.psiKernelMap`: the canonical map `𝒜_n ⟶ π_*i_*i^*𝒪_P(n)`
  attached to `ψ`.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.squareComparison_inv_comp_map_comp_eq_of_chartPullbackIso`:
  the chart property of `ψ`, decomposed through the square comparison.
* `AlgebraicGeometry.Space.C1359Bridge.psiKernelMap_etalePointReading_eq_zero_iff`: the canonical
  map on the reading of a section is the adjoint of `ψ ≫ η_i` on its 03LW-reading.
* `AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_iff_psiKernelMap`: **the chart
  dictionary at the atlas**.

## Implementation notes

The steps are stated through the regular functions `valAppSection`, `smallPieceRead`,
`modulesHomSection` and the predicate `pullbackSectionVanishes`, and the base of the relative Proj
of the chart is spelled over the scheme of the situation (`toRelativeProjOver`): the same sections
in the spellings produced by the different steps are then compared argument by argument.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section of the target of a morphism of sheaves of modules, as a regular function of the
morphism, the object and the section. -/
def valAppSection {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V) : N.val.obj V :=
  φ.val.app V x

/-- A section of a homogeneous piece, read through the comparison with the re-presented piece, as a
regular function of the section. -/
def smallPieceRead {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} R) (n : ℤ) (V : Cᵒᵖ)
    (y : (A.smallPiece n).val.obj V) : (A.piece n).val.obj V :=
  SheafOfModules.GradedAlgebra.smallPieceEquiv A n V y

/-- The vanishing of the pullback of a local section along a morphism of schemes, as a regular
predicate of its data. -/
def pullbackSectionVanishes {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) (U : X.Opens)
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : F.val.obj (op U)) : Prop :=
  Scheme.Modules.pullbackSection f F U V h a = 0

/-- The component at an open of a morphism of modules on a scheme, as a regular function. -/
def modulesHomSection {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (V : X.Opens)
    (y : M.val.obj (op V)) : N.val.obj (op V) :=
  φ.val.app (op V) y

section SchemeGeneric

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

variable {Y P : Scheme.{u}} (A : SheafGradedAlgebra Y) (ι : P ⟶ (relativeProj A).scheme)

/-- `AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_iff_pullbackAdjointPsi`, with the
vanishing written through `AlgebraicGeometry.Space.C1359Bridge.pullbackSectionVanishes`. -/
theorem mem_twistKerGradedIdeal_iff_pullbackSectionVanishes {Z : Scheme.{u}} (j : Z ⟶ P)
    [AlgebraicGeometry.IsClosedImmersion (j ≫ ι)]
    [AlgebraicGeometry.QuasiCompact (relativeProj A).toBase] (p : P ⟶ Y)
    (hp : p = ι ≫ (relativeProj A).toBase) (n : ℕ) (W : Y.Opens)
    (hV' : ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W) ≤ p ⁻¹ᵁ W) (a : Γ(A.piece (n : ℤ), W)) :
    a ∈ ((twistKerGradedIdeal A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) (j ≫ ι)).piece
        (n : ℤ)).toSubmodule.obj (op W) ↔
      pullbackSectionVanishes j
        ((Scheme.Modules.pullback ι).obj ((Tag07ZGTwist.twistAlgebra A).piece (n : ℤ)))
        (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) (j ⁻¹ᵁ (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
        le_rfl (modulesHomSection (pullbackAdjointPsi A ι p hp n)
          (ι ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W))
          (Scheme.Modules.pullbackSection p (A.piece (n : ℤ)) W _ hV' a)) :=
  mem_twistKerGradedIdeal_iff_pullbackAdjointPsi A ι j p hp n W hV' a

end SchemeGeneric

section Points

attribute [local irreducible] CategoryTheory.yoneda

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) {U₀ : BigFppfOver B S hS} (u₀ : yoneda.obj U₀ ⟶ X.1)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

variable {c : (⟨yoneda.obj (d.fibre U₀ u₀), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩}
  (hsq : IsPullback c (representedSpaceMap B S hS (d.fibreHom U₀ u₀))
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) (pointHom u₀))
  (comm : c ≫ (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
    representedSpaceMap B S hS (d.fibreHom U₀ u₀) ≫ pointHom u₀)

/-- The identification `c^*(π^*𝒜_n) ≅ (π_U^*(u^*𝒜)_n)^a` along `c : U ×_X P ⟶ P` over a scheme
point `u : U ⟶ X` (`AlgebraicGeometry.Space.pointChainPullbackIso`), read with `u^*𝒜_n` as an
inverse image, is the square comparison followed by the inverse image of the Zariski reading and
of an attached module. -/
theorem pointChainPullbackIso_eq_squareComparison (n : ℤ) :
    (pointChainPullbackIso (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) A hA
        c (d.fibreHom U₀ u₀) u₀ comm n :
      (modulePullback B S hS c).obj ((modulePullback B S hS
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
        ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
          (quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
            (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
                (pointHom u₀) _ (hA n))))).obj) =
      (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c comm).app (A.piece n) ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).mapIso
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) := by
  refine Eq.trans ?_ (congrArg (· ≪≫ _) (squareComparison_app_eq
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c comm (A.piece n))).symm
  refine Eq.trans ?_ (Iso.trans_assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≪≫ ·) (Iso.trans_assoc _ _ _)).symm
  rfl

/-- The paste of the chart property through an isomorphism equation. -/
private theorem paste_chartIso {C : Type*} [Category C] {X₀ X₁ X₃ X₄ X₅ : C}
    (e₁ : X₁ ≅ X₀) (R : X₀ ≅ X₃) (c : X₁ ≅ X₃) (hc : c = e₁ ≪≫ R)
    (ψ : X₁ ⟶ X₄) (χh : X₄ ⟶ X₅) (E : X₃ ⟶ X₅) (hψ : ψ ≫ χh = c.hom ≫ E) :
    e₁.inv ≫ ψ ≫ χh = R.hom ≫ E := by
  subst hc
  rw [hψ]
  simp

/-- **The chart property of `ψ` in decomposed form**, along `c : U ×_X P ⟶ P` over a scheme point
`u : U ⟶ X`: if `c^*ψ` read through `χ : c^*𝒦 ≅ M₂^a` is the identification
`AlgebraicGeometry.Space.pointChainPullbackIso` followed by the module attached to `Ψ`, then the
square comparison followed by `c^*ψ` and `χ` is the inverse image of the Zariski reading and of an
attached module followed by the module attached to `Ψ`. -/
theorem squareComparison_inv_comp_map_comp_eq_of_pointChainPullbackIso (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS c).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((etalePointAlgebra A U₀ u₀).piece n)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA u₀ n)) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullback B S hS c).map ψ ≫ χ.hom =
      (pointChainPullbackIso (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) A
        hA c (d.fibreHom U₀ u₀) u₀ comm n).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom) :
    (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c comm).inv.app
        (A.piece n) ≫ (modulePullback B S hS c).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom :=
  paste_chartIso _ _ _ (pointChainPullbackIso_eq_squareComparison d u₀ hP A hA comm n) _ _ _ hψ

include hsq in
/-- `AlgebraicGeometry.Space.C1359Bridge.homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff`,
with the 03LW-reading written through `AlgebraicGeometry.Space.C1359Bridge.valAppSection`. -/
theorem homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff_valAppSection
    (hc : IsEtale B S hS c.hom)
    (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS c).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
        comm).inv.app (A.piece n) ≫ (modulePullback B S hS c).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ ⟨P, hP⟩) {T'' : BigFppfOver B S hS}
    (cZ : (⟨yoneda.obj T'', isAlgebraicSpace_yoneda B S hS T''⟩ : AlgebraicSpaces B S hS) ⟶ Z)
    (τZ : T'' ⟶ d.fibre U₀ u₀)
    (sqZ : IsPullback cZ (representedSpaceMap B S hS τZ) i c)
    (hg : IsEtale B S hS (pointHom u₀).hom)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj (d.fibre U₀ u₀)).Opens)
    (hV : V = (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (V'' : ((BigFppfOver.toScheme B S hS).obj T'').Opens)
    (hV'' : V'' = (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (hV''' : V'' ≤ (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (x : ((modulePullback B S hS (pointHom u₀)).obj (A.piece n)).val.obj
      (op ((selfOpensFunctor B S hS U₀).obj W))) :
    ((modulePullbackAdjunction B S hS
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).homEquiv _ _
        (ψ ≫ (modulePullbackAdjunction B S hS i).unit.app K)).val.app
        (op ((smallEtalePostcomp B S hS (pointHom u₀) hg).obj
          ((selfOpensFunctor B S hS U₀).obj W)))
        (valAppSection ((modulePullbackIsoEtaleModulePullback B S hS (pointHom u₀)
          hg).app (A.piece n)).hom (op ((selfOpensFunctor B S hS U₀).obj W)) x) = 0 ↔
      pullbackSectionVanishes ((BigFppfOver.toScheme B S hS).map τZ) M₂.obj V V'' hV'''
        (modulesHomSection Ψ.hom V
          (Scheme.Modules.pullbackSection
            ((BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀))
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U₀)).obj
              ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))) W V hV' x)) :=
  homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff d u₀ hP A hA hsq comm hc n M₂ χ Ψ ψ hψ i cZ
    τZ sqZ hg W V hV hV' V'' hV'' hV''' x

end Points

section PointsAtlas

attribute [local irreducible] CategoryTheory.yoneda

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- **The chart property of `ψ` in decomposed form.** -/
theorem squareComparison_inv_comp_map_comp_eq_of_chartPullbackIso (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace)
      (presentationPointPieceQcoh Px A hA n) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map ψ ≫
        χ.hom = (d.chartPullbackIso Px hP A hA n).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre Px.U Px.toSpace)).functor.map Ψ).hom) :
    (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom Px.toSpace) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
        (presentationFibreAtlas d Px hP)
        (d.presentationAtlas_comp_homMk Px hP)).inv.app (A.piece n) ≫
      (modulePullback B S hS (presentationFibreAtlas d Px hP)).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).map
        (zariskiReadingQuasicoherentIso Px.U
          ((modulePullback B S hS (pointHom Px.toSpace)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom Px.toSpace) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom Px.U Px.toSpace)
          (zariskiReadingQcoh Px.U ((modulePullback B S hS (pointHom Px.toSpace)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom Px.toSpace) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre Px.U Px.toSpace)).functor.map Ψ).hom := by
  have h0 : (d.chartPullbackIso Px hP A hA n :
      (modulePullback B S hS (presentationFibreAtlas d Px hP)).obj
          ((modulePullback B S hS
            (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
        ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
          (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace)
            (zariskiReadingQcoh Px.U ((modulePullback B S hS (pointHom Px.toSpace)).obj (A.piece n))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
                (pointHom Px.toSpace) _ (hA n))))).obj) =
      pointChainPullbackIso (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) A hA
        (presentationFibreAtlas d Px hP) (d.fibreHom Px.U Px.toSpace) Px.toSpace
        (d.presentationAtlas_comp_homMk Px hP) n := rfl
  have h1 := h0.trans (pointChainPullbackIso_eq_squareComparison d Px.toSpace hP A hA
    (c := presentationFibreAtlas d Px hP) (d.presentationAtlas_comp_homMk Px hP) n)
  exact paste_chartIso _ _ _ h1 _ _ _ hψ


end PointsAtlas

section Situation1

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)

/-- **The canonical map `𝒜_n ⟶ π_*i_*i^*𝒪_P(n)`** attached to `ψ : π^*𝒜_n ⟶ 𝒪_P(n)`. -/
def psiKernelMap (n : ℕ) (ψ : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj) :=
  (s.smallAlgebraPieceIso (n : ℤ)).inv ≫
    (modulePullbackAdjunction s.site s.base s.containsBase
      (ObjectProperty.homMk s.relativeProjπ :
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).homEquiv
      (s.shrink.algebra.piece (n : ℤ)) _
      (ψ ≫ (modulePullbackAdjunction s.site s.base s.containsBase (Y :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).unit.app
        (s.twistModule Px (n : ℤ)).obj)

local notation "MK" => RelativeProjSituation.mk s.site s.base s.containsBase s.space s.algebra
  s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT

/-- The reading of a section on a chart, through the comparison of Stacks 03LW. -/
theorem etalePointReading_eq_smallPieceRead {T₀ : BigFppfOver s.site s.base s.containsBase}
    (t₀ : yoneda.obj T₀ ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) t₀).hom)
    (n : ℤ) (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₀).Opens)
    (a : Γ((s.relativeProjPoints.algebra T₀ t₀).piece n, W)) :
    s.etalePointReading t₀ hf n W a =
      smallPieceRead s.algebra n (op ((MK).etalePointChart t₀ hf W))
        (valAppSection ((MK).etalePointIso t₀ hf n).hom
          (op ((selfOpensFunctor s.site s.base s.containsBase T₀).obj W))
          ((MK).etalePointSectionsUnfold t₀ n W a)) :=
  (etalePointReading_eq_mk s t₀ hf n W a).trans
    (RelativeProjSituation.etalePointSectionsEquiv_apply s.mul_comm s.negative_isZero
      s.isQuasicoherent s.sections_hasCardinalLT t₀ hf n W a)

/-- The canonical map on a section of the re-presented algebra read in `𝒜`. -/
theorem psiKernelMap_val_app_smallPieceRead (n : ℕ)
    (ψ : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (y : (s.algebra.smallPiece (n : ℤ)).val.obj V) :
    (psiKernelMap s Px i n ψ).val.app V (smallPieceRead s.algebra (n : ℤ) V y) =
      ((modulePullbackAdjunction s.site s.base s.containsBase
      (ObjectProperty.homMk s.relativeProjπ :
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).homEquiv
      (s.shrink.algebra.piece (n : ℤ)) _
      (ψ ≫ (modulePullbackAdjunction s.site s.base s.containsBase (Y :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).unit.app
        (s.twistModule Px (n : ℤ)).obj)).val.app V y :=
  congrArg (fun z => ((modulePullbackAdjunction s.site s.base s.containsBase
      (ObjectProperty.homMk s.relativeProjπ :
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).homEquiv
      (s.shrink.algebra.piece (n : ℤ)) _
      (ψ ≫ (modulePullbackAdjunction s.site s.base s.containsBase (Y :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).unit.app
        (s.twistModule Px (n : ℤ)).obj)).val.app V z)
    (smallAlgebraPieceIso_inv_smallPieceEquiv s (n : ℤ) V y)

/-- **The canonical map on the reading of a section of `u^*𝒜_n` on a chart `W ⟶ U ⟶ X`** is
the adjoint of `ψ ≫ η_i` on the 03LW-reading of the section. -/
theorem psiKernelMap_etalePointReading_eq_zero_iff (n : ℕ)
    (ψ : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj)
    {T₀ : BigFppfOver s.site s.base s.containsBase} (t₀ : yoneda.obj T₀ ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) t₀).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₀).Opens)
    (a : Γ((s.relativeProjPoints.algebra T₀ t₀).piece (n : ℤ), W)) :
    (psiKernelMap s Px i n ψ).val.app (op (s.etalePointChart t₀ hf W))
        (s.etalePointReading t₀ hf (n : ℤ) W a) = 0 ↔
      ((modulePullbackAdjunction s.site s.base s.containsBase
      (ObjectProperty.homMk s.relativeProjπ :
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).homEquiv
      (s.shrink.algebra.piece (n : ℤ)) _
      (ψ ≫ (modulePullbackAdjunction s.site s.base s.containsBase (Y :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).unit.app
        (s.twistModule Px (n : ℤ)).obj)).val.app (op
            ((smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) t₀)
        hf).obj ((selfOpensFunctor s.site s.base s.containsBase T₀).obj W))) (valAppSection
            ((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
            (pointHom (X := s.space) t₀) hf).app (s.shrink.algebra.piece (n : ℤ))).hom
          (op ((selfOpensFunctor s.site s.base s.containsBase T₀).obj W))
          (s.etalePointSectionsUnfold t₀ (n : ℤ) W a)) = 0 := by
  rw [etalePointReading_eq_smallPieceRead]
  exact Iff.of_eq (congrArg (· = 0) (psiKernelMap_val_app_smallPieceRead s Px i n ψ _ _))

end Situation1

section Situation2

attribute [local irreducible] CategoryTheory.yoneda

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- The identification `V ×_X P = Proj_V(v^*𝒜)` on schemes, with its target spelled over the scheme
of `V` of the situation. -/
abbrev toRelativeProjOver (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (S := (BigFppfOver.toScheme s.site s.base s.containsBase).obj V)
        (s.shrink.pointAlgebra V v)).scheme :=
  s.toRelativeProj V v

/-- Tag 01NR's `ψ` on the scheme of `V ×_X P`, in adjoint form, along
`AlgebraicGeometry.Space.C1359Bridge.toRelativeProjOver`. -/
abbrev chartAdjointPsiOver (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℕ) :=
  pullbackAdjointPsi (Y := (BigFppfOver.toScheme s.site s.base s.containsBase).obj V)
    (X := (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v))
    (s.shrink.pointAlgebra V v) (toRelativeProjOver s V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (s.relativeProjPoints.fibreHom V v))
    (s.toScheme_map_fibreHom V v) n

/-- **The chart dictionary for the kernel of `𝒜_n ⟶ π_*i_*i^*𝒪_P(n)` (Stacks 085L).**  At the
atlas `u : U ⟶ X`, a local section `a` of `(u^*𝒜)_n` over a Zariski open `W` lies in the graded
ideal of Tag 0801 of the closed subscheme `Z ×_X U ⊆ Proj_U(u^*𝒜)` exactly when the canonical
map attached to `ψ` kills the reading of `a` on the chart `W ⟶ U ⟶ X`. -/
theorem mem_twistKerGradedIdeal_iff_psiKernelMap
    [AlgebraicGeometry.QuasiCompact (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (s.relativeProjPoints.algebra Px.U Px.toSpace)).toBase] (n : ℕ)
    (ψ : (s.psiSourceQcoh (n : ℤ)).obj ⟶ (s.twistModule Px (n : ℤ)).obj)
    (hψ : (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        ψ ≫ (s.twistModuleChartIso Px (n : ℤ)).hom = s.psiChartHomOfAdjoint Px n)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) Px.toSpace).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U).Opens)
    (a : Γ((s.relativeProjPoints.algebra Px.U Px.toSpace).piece (n : ℤ), W)) :
    a ∈ ((Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
        (s.relativeProjPoints.algebra Px.U Px.toSpace)
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (RelativeProjSituation.chartClosedSubscheme i hi Px.U Px.toSpace)).piece
          (n : ℤ)).toSubmodule.obj (op W) ↔
      (psiKernelMap s Px i n ψ).val.app (op (s.etalePointChart Px.toSpace hf W))
        (s.etalePointReading Px.toSpace hf (n : ℤ) W a) = 0 := by
  have hψ' := squareComparison_inv_comp_map_comp_eq_of_chartPullbackIso s.relativeProjPoints Px
    s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent (n : ℤ)
    (⟨(Scheme.Modules.pullback (toRelativeProjOver s Px.U Px.toSpace)).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
        (s.shrink.pointAlgebra Px.U Px.toSpace)).piece (n : ℤ)),
      (s.twistPieceQcoh Px.U Px.toSpace (n : ℤ)).property⟩ :
      (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
    (s.twistModuleChartIso Px (n : ℤ))
    (ObjectProperty.homMk (chartAdjointPsiOver s Px.U Px.toSpace n)) ψ hψ
  have hV' : (toRelativeProjOver s Px.U Px.toSpace) ⁻¹ᵁ
      ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (S := (BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U)
        (s.shrink.pointAlgebra Px.U Px.toSpace)).toBase ⁻¹ᵁ W) ≤
      (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.fibreHom Px.U Px.toSpace) ⁻¹ᵁ W := by
    rw [s.toScheme_map_fibreHom Px.U Px.toSpace]; exact le_rfl
  have hch := homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff_valAppSection
    s.relativeProjPoints Px.toSpace
    s.isAlgebraicSpace_relativeProjFunctor s.shrink.algebra s.shrink.isQuasicoherent
    (isPullback_presentationFibreAtlas s.relativeProjPoints Px
      s.isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjPoints.presentationAtlas_comp_homMk Px s.isAlgebraicSpace_relativeProjFunctor)
    (presentationAtlas_isEtale _) (n : ℤ) _
    (s.twistModuleChartIso Px (n : ℤ))
    (ObjectProperty.homMk (chartAdjointPsiOver s Px.U Px.toSpace n)) ψ hψ' i _
    ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i hi).2.2.rep.snd
      (s.relativeProjPoints.fibreToSpace Px.U Px.toSpace))
    (isPullback_closedSubspaceChart s Px i hi) hf W
    _ (by rw [s.toScheme_map_fibreHom Px.U Px.toSpace]; rfl) hV' _ rfl le_rfl
    (s.etalePointSectionsUnfold Px.toSpace (n : ℤ) W a)
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
            (s.relativeProjPoints.fibreToSpace Px.U Px.toSpace)) ≫
                (toRelativeProjOver s Px.U Px.toSpace)) :=
    RelativeProjSituation.isClosedImmersion_chartClosedSubscheme i hi Px.U Px.toSpace
  have : AlgebraicGeometry.QuasiCompact (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (s.shrink.pointAlgebra Px.U Px.toSpace)).toBase := by assumption
  have h1 := mem_twistKerGradedIdeal_iff_pullbackSectionVanishes
    (Y := (BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U)
    (P := (BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre Px.U Px.toSpace)) (s.shrink.pointAlgebra Px.U Px.toSpace)
    (toRelativeProjOver s Px.U Px.toSpace)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
            (s.relativeProjPoints.fibreToSpace Px.U Px.toSpace)))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (s.relativeProjPoints.fibreHom Px.U Px.toSpace)) (s.toScheme_map_fibreHom Px.U Px.toSpace) n W
    hV' (s.etalePointSectionsUnfold Px.toSpace (n : ℤ) W a)
  exact h1.trans (hch.symm.trans
    (psiKernelMap_etalePointReading_eq_zero_iff s Px i n ψ Px.toSpace hf W a).symm)

end Situation2

end AlgebraicGeometry.Space.C1359Bridge

end
