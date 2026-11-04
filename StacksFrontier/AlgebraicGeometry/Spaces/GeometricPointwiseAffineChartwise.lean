module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion

/-!
# Conditions (1) and (2) of Stacks 0DKG, from the étale transport of the map 0DKF

Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces, `K`, `K'` with quasi-coherent
cohomology and `φ : L(g')^*K ⟶ K'`. Condition (1) of Stacks 0DKG, that the map of Equation 0DKF
is invertible at every geometric point of `X'`, is equivalent to its condition (2) read on affine
étale quadruples, given two inputs: the transport of the map 0DKF along étale morphisms of
squares, and its identification on a cartesian square of affine schemes with the composite of
Stacks 065Z. Both directions are per-point: (1) ⟹ (2) reads (1) at the images of the points of
`U'`, and (2) ⟹ (1) reads (2) on an affine quadruple through the given point.

## Main results

* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_iff_affineChartwiseBaseChange_of`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Conditions (1) and (2) of Stacks 0DKG are equivalent**, given the étale transport `hc` of
the map 0DKF and its identification `h42` on cartesian squares of affine schemes. -/
theorem geometricPointwiseBaseChange_iff_affineChartwiseBaseChange_of
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (hc : ∀ (U V V' U' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀),
      IsEtale B S hS a.hom → IsEtale B S hS b.hom → IsEtale B S hS c.hom →
      IsPullback g₀' f₀' f₀ g₀ →
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f →
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g →
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' →
      ∀ (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
      (x₁' : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ),
      IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' sq.w
        (geometricPointMap a'.hom x₁') K K' φ n) ↔
      IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x₁'
        ((smallEtaleDerivedModulePullback B S hS a).obj K)
        ((smallEtaleDerivedModulePullback B S hS a').obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS
            (representedSpaceMap B S hS g₀') a).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS a').map φ) n))
    (h42 : ∀ {U V V' U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀),
      IsPullback g₀' f₀' f₀ g₀ →
      ∀ (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))),
      QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K →
      ∀ (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))),
      QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K' →
      ∀ φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K',
      (∀ (x₁' : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ),
        IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
          x₁' K K' φ n)) ↔
        IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K K' φ)) :
    GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ ↔
      AffineChartwiseBaseChange B S hS f g f' g' sq.w K K' φ := by
  constructor
  · intro h1
    constructor
    intro U V V' U' _ _ _ _ a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc' hpb hfa hgb hfc ha'
    exact (h42 f₀ g₀ f₀' g₀' w₀ hpb _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a _ hK) _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' _ hK') _).1 fun x₁' n =>
      (hc U V V' U' a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc' hpb hfa hgb hfc ha' x₁' n).1 (h1 _ n)
  · intro h2 x' n
    obtain ⟨U, V, V', U', hU, hV, hV', hU', a, b, c, a', f₀, g₀, f₀', g₀', ha, hb, hc', hpb, hfa,
      hgb, hfc, ha', x'', rfl⟩ := exists_affineQuadruple_geometricPoint sq x'
    exact (hc U V V' U' a b c a' f₀ g₀ f₀' g₀' hpb.w ha hb hc' hpb hfa hgb hfc ha' x'' n).2
      ((h42 f₀ g₀ f₀' g₀' hpb.w hpb _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a _ hK) _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' _ hK') _).2
        (h2.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' hpb.w ha hb hc' hpb hfa hgb hfc ha') x'' n)

end AlgebraicGeometry.Space
