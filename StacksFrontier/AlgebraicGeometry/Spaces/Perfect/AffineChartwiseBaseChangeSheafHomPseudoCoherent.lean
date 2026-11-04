module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensorSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.HasFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartBaseChangeSheafHomPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackSheafHomMapEtaleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality
public meta import StacksFrontier.Tactic.HEqCongr

public import StacksFrontier.Tactic.HEqCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturalitySupplement
/-!
# Condition (2) of Stacks 0DKG for the derived internal Hom out of a pseudo-coherent object

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces with `g` of finite Tor
dimension, `K` bounded below with quasi-coherent cohomology, `K'` with quasi-coherent cohomology
and `φ : L(g')^*K ⟶ K'`. For `E` pseudo-coherent on `X`, condition (2) of Stacks 0DKG passes from
`(K, K', φ)` to `R𝓗om(E, K)`, `R𝓗om(L(g')^*E, K')` and the map of Stacks 08JF followed by `φ`.

On an affine étale quadruple `(a, b, c, a')` the condition for `R𝓗om(E, K)` is transported along
the maps of Stacks 08JF along the étale morphisms `a`, `a'` to the condition for
`R𝓗om(a^*E, a^*K)` on the square of affine schemes.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineSectionsBaseChangeComp_pullback_sheafHom_iff`:
  the transport to the affine square.
* `AlgebraicGeometry.Space.affineChartwiseBaseChange_sheafHom_of_isPseudoCoherent`: condition (2)
  of Stacks 0DKG passes to `R𝓗om(E, K)` for `E` pseudo-coherent, `K` bounded below and `g` of
  finite Tor dimension.

## References

* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `isIso_representedAffineSectionsBaseChangeComp_iff_of_iso` for invertible morphisms. -/
theorem isIso_representedAffineSectionsBaseChangeComp_iff_of_isIso
    {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))}
    {K₁' K₂' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))}
    (e : K₁ ⟶ K₂) [IsIso e] (e' : K₁' ⟶ K₂') [IsIso e']
    (φ₁ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K₁ ⟶ K₁')
    (φ₂ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K₂ ⟶ K₂')
    (h : φ₁ ≫ e' =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map e ≫ φ₂) :
    IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K₁ K₁' φ₁) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K₂ K₂' φ₂) :=
  isIso_representedAffineSectionsBaseChangeComp_iff_of_iso f₀ g₀ f₀' g₀' w₀ (asIso e) (asIso e')
    φ₁ φ₂ h

/-- **Derived pullback along an étale morphism preserves boundedness below**: it is étale
restriction on derived categories, an exact functor commuting with cohomology. -/
theorem isBoundedBelow_smallEtaleDerivedModulePullback_of_isEtale {X₀ Y₀ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ Y₀) (ha : IsEtale B S hS a.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₀)))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow ((smallEtaleDerivedModulePullback B S hS a).obj K) := by
  have := etaleModulePullback_additive B S hS a ha
  have := preservesFiniteLimits_etaleModulePullback B S hS a ha
  have := preservesFiniteColimits_etaleModulePullback B S hS a ha
  obtain ⟨n₀, hn₀⟩ := hK
  refine DerivedCategoryB.isBoundedBelow_of_iso
    ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K).symm ⟨n₀, fun n hn => ?_⟩
  exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (etaleModulePullback.{u, u} B S hS a ha) n).app K).isZero_iff.mpr
      ((etaleModulePullback.{u, u} B S hS a ha).map_isZero (hn₀ n hn))

/-- The transpose of the map of Stacks 08JF on algebraic spaces is the inverse of Stacks 07A4
followed by the pullback of the evaluation. -/
theorem homEquiv_symm_smallEtaleDerivedPullbackSheafHomMap {X₀ X₀' : AlgebraicSpaces B S hS}
    (h : X₀' ⟶ X₀)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀))) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X₀'
        ((smallEtaleDerivedModulePullback B S hS h).obj E)).homEquiv _ _).symm
        (smallEtaleDerivedPullbackSheafHomMap h E K) =
      (smallEtaleDerivedPullbackTensorIso h).inv.app
          (((smallEtaleDerivedSheafHom B S hS X₀).obj (op E)).obj K, E) ≫
        (smallEtaleDerivedModulePullback B S hS h).map
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X₀ E).counit.app K) := by
  rw [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit, Equiv.symm_apply_apply]

variable {X X' : AlgebraicSpaces B S hS} (g' : X' ⟶ X)

/-- **The chartwise condition for `R𝓗om(E, K)`, transported to the affine square.** On an affine
square `g₀' ≫ f₀ = f₀' ≫ g₀` with étale `a : U ⟶ X`, `a' : U' ⟶ X'` and `g₀' ≫ a = a' ≫ g'`,
if the maps of Stacks 08JF along `a` at `(E, K)` and along `a'` at `(L(g')^*E, K')` are
invertible, the composite of Stacks 065Z for `a^*R𝓗om(E, K)`, `(a')^*R𝓗om(L(g')^*E, K')` and
the pullback of `08JF ≫ R𝓗om(1, φ)` is invertible exactly when the one for `R𝓗om(a^*E, a^*K)`,
`R𝓗om(L(g₀')^*a^*E, (a')^*K')` and `08JF ≫ R𝓗om(1, φ₀)` is, `φ₀` the pullback of `φ`. -/
theorem isIso_representedAffineSectionsBaseChangeComp_pullback_sheafHom_iff
    {U V V' U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    [IsIso (smallEtaleDerivedPullbackSheafHomMap a E K)]
    [IsIso (smallEtaleDerivedPullbackSheafHomMap a'
      ((smallEtaleDerivedModulePullback B S hS g').obj E) K')] :
    IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀
        ((smallEtaleDerivedModulePullback B S hS a).obj
          (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K))
        ((smallEtaleDerivedModulePullback B S hS a').obj
          (((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K'))
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullback B S hS a').map
            (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
              ((smallEtaleDerivedSheafHom B S hS X').obj
                (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ))) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀
        (((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          (op ((smallEtaleDerivedModulePullback B S hS a).obj E))).obj
            ((smallEtaleDerivedModulePullback B S hS a).obj K))
        (((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          (op ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
            ((smallEtaleDerivedModulePullback B S hS a).obj E)))).obj
              ((smallEtaleDerivedModulePullback B S hS a').obj K'))
        (smallEtaleDerivedPullbackSheafHomMap (representedSpaceMap B S hS g₀')
            ((smallEtaleDerivedModulePullback B S hS a).obj E)
            ((smallEtaleDerivedModulePullback B S hS a).obj K) ≫
          ((smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            (op ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
              ((smallEtaleDerivedModulePullback B S hS a).obj E)))).map
            ((smallEtaleDerivedModulePullbackCompIso B S hS
                (representedSpaceMap B S hS g₀') a).hom.app K ≫
              (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
              (smallEtaleDerivedModulePullback B S hS a').map φ))) :=
  CategoryTheory.PullbackInternalHom.chart_iff_of_homEquiv_symm_of_comp
    (smallEtaleDerivedModulePullbackCompIso B S hS a' g')
    (smallEtaleDerivedModulePullbackSquareIso B S hS a g' a' (representedSpaceMap B S hS g₀') ha')
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (smallEtaleDerivedPullbackTensorIso a) (smallEtaleDerivedPullbackTensorIso a')
    (smallEtaleDerivedPullbackTensorIso g')
    (smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀'))
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (smallEtaleDerivedSheafHom B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (fun Z => (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀' ≫ a)).obj Z)
    (fun Z => (smallEtaleDerivedModulePullback B S hS (a' ≫ g')).obj Z)
    (fun Z =>
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom.app Z)
    (fun Z => (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app Z)
    (fun Z => (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app Z)
    (fun Z => eq_of_heq (HEq.trans (by heq_congr_full) (HEq.trans
      (heq_of_eq (Stacks.Generic.squareCompositeIso_inv_app_trans
        (smallEtaleDerivedModulePullbackCompIso B S hS a' g')
        (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a)
        (smallEtaleDerivedModulePullbackCongr B S hS ha') Z)) (by heq_congr_full))))
    (fun K₁ K₁' φ₁ =>
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K₁ K₁' φ₁))
    (fun e _ e' _ φ₁ φ₂ h => isIso_representedAffineSectionsBaseChangeComp_iff_of_isIso f₀ g₀ f₀'
      g₀' w₀ e e' φ₁ φ₂ h) E K φ
    (smallEtaleDerivedPullbackSheafHomMap a E K)
    (homEquiv_symm_smallEtaleDerivedPullbackSheafHomMap a E K)
    (smallEtaleDerivedPullbackSheafHomMap g' E K)
    (homEquiv_symm_smallEtaleDerivedPullbackSheafHomMap g' E K)
    (smallEtaleDerivedPullbackSheafHomMap a' ((smallEtaleDerivedModulePullback B S hS g').obj E) K')
    (homEquiv_symm_smallEtaleDerivedPullbackSheafHomMap a'
      ((smallEtaleDerivedModulePullback B S hS g').obj E) K')
    (smallEtaleDerivedPullbackSheafHomMap (representedSpaceMap B S hS g₀')
      ((smallEtaleDerivedModulePullback B S hS a).obj E)
      ((smallEtaleDerivedModulePullback B S hS a).obj K))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (homEquiv_symm_smallEtaleDerivedPullbackSheafHomMap (representedSpaceMap B S hS g₀')
        ((smallEtaleDerivedModulePullback B S hS a).obj E)
        ((smallEtaleDerivedModulePullback B S hS a).obj K)))
      (by heq_congr))))
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso a g' a'
      (representedSpaceMap B S hS g₀') ha' _ E)
    (fun v _ _ θ => smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinaturality
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ v θ)

/-- **Condition (2) of Stacks 0DKG passes to the derived internal Hom out of a pseudo-coherent
object** (Stacks 0DKI (3), with `g` of finite Tor dimension, on affine étale quadruples). For a
cartesian square with `g` of finite Tor dimension, `E` pseudo-coherent and `K` bounded below with
quasi-coherent cohomology on `X`, `K'` with quasi-coherent cohomology on `X'` and
`φ : L(g')^*K ⟶ K'`: if condition (2) of Stacks 0DKG holds for `(K, K', φ)`, it holds for
`R𝓗om(E, K)`, `R𝓗om(L(g')^*E, K')` and the map of Stacks 08JF followed by `R𝓗om(L(g')^*E, φ)`. -/
theorem affineChartwiseBaseChange_sheafHom_of_isPseudoCoherent {Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    (hg : HasFiniteTorDimension g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : AffineChartwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    AffineChartwiseBaseChange B S hS f g f' g' sq.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
      (((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
      (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
        ((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ) := by
  refine ⟨fun U V V' U' _ _ _ _ a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁ h₂ h₃ ha' => ?_⟩
  have ha'e : IsEtale B S hS a'.hom :=
    isEtale_of_isPullback_of_etaleQuadruple B S hS sq ha hb hc
      (isPullback_representedSpaceMap B S hS hpb) h₁ h₂ h₃ ha'
  have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale a ha E K
  have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale a' ha'e
    ((smallEtaleDerivedModulePullback B S hS g').obj E) K'
  refine (isIso_representedAffineSectionsBaseChangeComp_pullback_sheafHom_iff g' a a' f₀ g₀ f₀' g₀'
    w₀ ha' E K K' φ).mpr ?_
  exact isIso_representedAffineSectionsBaseChangeComp_sheafHom_of_isPseudoCoherent B S hS
    f₀ g₀ f₀' g₀' w₀ hpb (hg.hasFiniteTorDimensionRingHom V V' b c g₀ hb hc h₂)
    ((smallEtaleDerivedModulePullback B S hS a).obj E)
    (isPseudoCoherent_smallEtaleDerivedModulePullback a E hE)
    ((smallEtaleDerivedModulePullback B S hS a).obj K)
    ⟨isBoundedBelow_smallEtaleDerivedModulePullback_of_isEtale a ha K hK.1,
      derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK.2⟩
    ((smallEtaleDerivedModulePullback B S hS a').obj K')
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK') _
    (h.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁ h₂ h₃ ha')

end AlgebraicGeometry.Space

end
