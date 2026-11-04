module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapEtaleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartwiseBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartwiseBaseChangeSheafHomPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap

/-!
# Stacks 0DKI: the conditions of Stacks 0DKG for tensor products and internal Homs

Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces, `K ∈ D_QCoh(𝒪_X)`,
`K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` satisfying the equivalent conditions of
Stacks 0DKG, read as invertibility of the map of Equation 0DKF at every geometric point. Then
the conditions hold for
1. `L(g')^*(E ⊗ᴸ K) ⟶ L(g')^*E ⊗ᴸ K'`, for `E ∈ D_QCoh(𝒪_X)`;
2. `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, the map of Stacks 08JF followed by `φ`, for `E`
   perfect;
3. the same map, for `E` pseudo-coherent and `K` bounded below, **provided `g` has finite Tor
   dimension** (`AlgebraicGeometry.Space.HasFiniteTorDimension`).
All three are read on affine étale quadruples through
`AlgebraicGeometry.Space.geometricPointwiseBaseChange_iff_affineChartwiseBaseChange`.

## Stacks 0DKI (3) is false as written

Part (3) fails without a condition on `g`. For `A = ℤ/4`, `X = Y = S = Spec A`, `f = id`,
`g = g' : Spec ℤ/2 ⟶ S` the closed point, `K = 𝒪_X`, `K' = L(g')^*K`, `φ = 𝟙` and `E = (ℤ/2)^~`
(pseudo-coherent), the conditions of Stacks 0DKG hold for `φ`, but not for
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`. As `A` is self-injective, `R𝓗om(E, K)` lies in degrees
`≤ 0`, while `H^1(R𝓗om(L(g')^*E, K'))` contains `Ext^1_A(ℤ/2, ℤ/2) ≠ 0`. This is formalized as
`not_forall_geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent` in the namespace
`Stacks.Examples.PseudoCoherentSheafHomBaseChange`. The proof in the source breaks where it
identifies `Hom^•(E_x, K_x) ⊗ᴸ R'` with `Hom^•(E_x, K_x ⊗ᴸ R')` for a bounded above complex of
finite free modules `E_x`: the infinite products in the Hom complex commute with `⊗ᴸ R'` only when
`R'` has finite Tor dimension. With `g` of finite Tor dimension the statement holds, and no
boundedness of `K'` is needed: on every affine étale chart it follows from the conditions for
`(K, K', φ)`.

## Main results

* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_tensor`: Stacks 0DKI (1).
* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_sheafHom_of_isPerfect`: Stacks 0DKI (2).
* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent`:
  Stacks 0DKI (3), corrected: `g` of finite Tor dimension.
* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_tensor_and_sheafHom`: the three together.

## References

* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The conditions of Stacks 0DKG pass to derived tensor products** (Stacks 0DKI (1)). For a
cartesian square, `E`, `K` with quasi-coherent cohomology on `X`, `K'` on `X'` and
`φ : L(g')^*K ⟶ K'` satisfying the conditions of Stacks 0DKG, they hold for
`L(g')^*(E ⊗ᴸ K) ⟶ L(g')^*E ⊗ᴸ K'`, Stacks 07A4 followed by `L(g')^*E ⊗ᴸ φ`. -/
@[stacks 0DKI "(1)"]
theorem geometricPointwiseBaseChange_tensor (sq : IsPullback g' f' f g)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    GeometricPointwiseBaseChange B S hS f g f' g' sq.w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
      (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ) :=
  (geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq _
    (qcohDerived_smallEtaleDerivedTensor_obj B S hS X E K hE hK) _
    (qcohDerived_smallEtaleDerivedTensor_obj B S hS X' _ K'
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g' E hE) hK') _).2
    (affineChartwiseBaseChange_tensor B S hS f g f' g' sq.w E K hE hK K' hK' φ
      ((geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq K hK K' hK' φ).1 h))

/-- **The conditions of Stacks 0DKG pass to the derived internal Hom out of a perfect object**
(Stacks 0DKI (2)). For a cartesian square, `E` perfect and `K` with quasi-coherent cohomology on
`X`, `K'` with quasi-coherent cohomology on `X'` and `φ : L(g')^*K ⟶ K'` satisfying the conditions
of Stacks 0DKG, they hold for `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, the map of Stacks 08JF
followed by `R𝓗om(L(g')^*E, φ)`. -/
@[stacks 0DKI "(2)"]
theorem geometricPointwiseBaseChange_sheafHom_of_isPerfect (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    GeometricPointwiseBaseChange B S hS f g f' g' sq.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
      (((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
      (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
        ((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ) :=
  (geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq _
    (qcohDerived_smallEtaleDerivedSheafHom X E K (Or.inr ⟨hE, hK⟩)) _
    (qcohDerived_smallEtaleDerivedSheafHom X' _ K'
      (Or.inr ⟨isPerfect_smallEtaleDerivedModulePullback g' E hE, hK'⟩)) _).2
    (affineChartwiseBaseChange_sheafHom_of_isPerfect f g f' g' sq.w E hE K hK K' hK' φ
      ((geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq K hK K' hK' φ).1 h))

/-- **The conditions of Stacks 0DKG pass to the derived internal Hom out of a pseudo-coherent
object, for `g` of finite Tor dimension** (Stacks 0DKI (3), corrected). Part (3) of the source has
no condition on `g` and is false as written: see
`not_forall_geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent` in the namespace
`Stacks.Examples.PseudoCoherentSheafHomBaseChange` (`A = ℤ/4`, `g : Spec ℤ/2 ⟶ Spec A`, where the
map of Equation 0DKF fails in degree `1`). The source proof commutes the infinite products of
`Hom^•(E_x, K_x)` with `⊗ᴸ R'`, which needs `R'` of finite Tor dimension. No boundedness of `K'` is
assumed: on every affine étale chart it follows from the conditions for `(K, K', φ)`. -/
@[stacks 0DKI "(3), corrected: g of finite Tor dimension added; (3) as written is false, see \
Stacks.Examples.PseudoCoherentSheafHomBaseChange"]
theorem geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent (sq : IsPullback g' f' f g)
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
    (h : GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    GeometricPointwiseBaseChange B S hS f g f' g' sq.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
      (((smallEtaleDerivedSheafHom B S hS X').obj
        (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
      (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
        ((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ) := by
  have hA := (geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq K hK.2 K' hK' φ).1 h
  have hH := affineChartwiseBaseChange_sheafHom_of_isPseudoCoherent g' f g f' sq hg E hE K hK K'
    hK' φ hA
  intro x' n
  obtain ⟨U, V, V', U', hU, hV, hV', hU', a, b, c, a', f₀, g₀, f₀', g₀', ha, hb, hc', hpb, hfa,
    hgb, hfc, ha', x'', hx''⟩ := exists_affineQuadruple_geometricPoint sq x'
  have ha'e : IsEtale B S hS a'.hom :=
    isEtale_of_isPullback_of_etaleQuadruple B S hS sq ha hb hc'
      (isPullback_representedSpaceMap B S hS hpb) hfa hgb hfc ha'
  have hQ₁ := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a _
    (qcohDerived_smallEtaleDerivedSheafHom X E K (Or.inl ⟨hE, hK⟩))
  have hQ₂ : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
      ((smallEtaleDerivedModulePullback B S hS a').obj
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')) := by
    have hfin := hg.hasFiniteTorDimensionRingHom V V' b c g₀ hb hc' hgb
    have hM : DerivedCategoryB.derivedCategoryBPlus
        (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O)))
        ((smallEtaleDerivedModulePullback B S hS a).obj K) :=
      ⟨isBoundedBelow_smallEtaleDerivedModulePullback_of_isEtale a ha K hK.1,
        derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK.2⟩
    have hM' := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'
    have hf : IsAffineHom B S hS (representedSpaceMap B S hS f₀).hom :=
      isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U inferInstance)
        (isAffineSpace_yoneda B S hS V inferInstance)
    have hg₀ : IsAffineHom B S hS (representedSpaceMap B S hS g₀).hom :=
      isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS V' inferInstance)
        (isAffineSpace_yoneda B S hS V inferInstance)
    have hBC := (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀'
      hpb.w _ hM.2 _ hM' _).2 (hA.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' hpb.w ha hb hc' hpb hfa hgb
        hfc ha')
    have hKt := isIso_smallEtaleTensorBaseChangeCompMap_of_isIso B S hS _ _ _ _
      (isPullback_representedSpaceMap B S hS hpb) (isQuasiCompact_of_isAffineHom_hom _ hf)
      (isQuasiSeparated_of_isAffineHom_hom _ hf) (isQuasiCompact_of_isAffineHom_hom _ hg₀)
      (isQuasiSeparated_of_isAffineHom_hom _ hg₀) (isAffineSpace_yoneda B S hS U inferInstance)
      _ hM.2 _ hM' _ hBC
    have hbb := isBoundedBelow_of_isIso_smallEtaleTensorBaseChangeCompMap_representedAffine B S hS
      f₀ g₀ f₀' g₀' hpb.w hfin _ hM _ hM' _ hKt
    have hH := qcohDerived_smallEtaleDerivedSheafHom
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
      ((smallEtaleDerivedModulePullback B S hS a').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E))
      ((smallEtaleDerivedModulePullback B S hS a').obj K')
      (Or.inl ⟨isPseudoCoherent_smallEtaleDerivedModulePullback a' _
        (isPseudoCoherent_smallEtaleDerivedModulePullback g' E hE), ⟨hbb, hM'⟩⟩)
    have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale a' ha'e
      ((smallEtaleDerivedModulePullback B S hS g').obj E) K'
    exact (QcohDerived B S hS _).prop_of_iso
      (asIso (smallEtaleDerivedPullbackSheafHomMap a'
        ((smallEtaleDerivedModulePullback B S hS g').obj E) K')).symm hH
  have hI := hH.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' hpb.w ha hb hc' hpb hfa hgb hfc ha'
  have hP := (forall_isIso_geometricStalkBaseChangeCohomologyMap_iff_isIso_representedAffineSectionsBaseChangeComp
    B S hS f₀ g₀ f₀' g₀' hpb.w hpb _ hQ₁ _ hQ₂ _).2 hI x'' n
  have h' := (isIso_geometricStalkBaseChangeCohomologyMap_iff_affineQuadruple sq _ _ _ U V V' U'
    a b c a' f₀ g₀ f₀' g₀' hpb.w ha hb hc' hpb hfa hgb hfc ha' x'' n).2 hP
  rw [hx''] at h'
  exact h'

/-- **Stacks 0DKI**, with `g` of finite Tor dimension added in part (3). For a cartesian square
`g' ≫ f = f' ≫ g` of algebraic spaces, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'` satisfying the conditions of Stacks 0DKG, these conditions hold
1. for `L(g')^*(E ⊗ᴸ K) ⟶ L(g')^*E ⊗ᴸ K'` (Stacks 07A4 followed by `φ`), `E ∈ D_QCoh(𝒪_X)`;
2. for `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` (Stacks 08JF followed by `φ`), `E` perfect;
3. for the same map, `E` pseudo-coherent, `K` bounded below and `g` of finite Tor dimension.

Part (3) of the source, without the condition on `g`, is false: for `k` separably closed,
`A = k[x]/(x²)`, `X = Y = S = Spec A`, `f = id`, `g : Spec k ⟶ S` the closed point, `K = 𝒪_X`,
`K' = 𝒪_{X'}`, `φ` the canonical isomorphism and `E = k`, in degree `-1` the map of Equation 0DKF
is `k ⟶ 0` (`H^{-1}(k ⊗ᴸ_A k) = k`, while `RHom_k(k ⊗ᴸ_A k, k)` lives in degrees `≥ 0`). The
source proof fails where it commutes the infinite products of `Hom^•(E_x, K_x)` with `⊗ᴸ R'`,
which needs `R'` of finite Tor dimension. No boundedness of `K'` is assumed. -/
theorem geometricPointwiseBaseChange_tensor_and_sheafHom (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    (∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))),
      QcohDerived B S hS X E →
      GeometricPointwiseBaseChange B S hS f g f' g' sq.w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
        (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')
        ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
          ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ)) ∧
    (∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E →
      GeometricPointwiseBaseChange B S hS f g f' g' sq.w
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
        (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
          ((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ)) ∧
    (HasFiniteTorDimension g → DerivedCategoryB.IsBoundedBelow K →
      ∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))),
      RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      GeometricPointwiseBaseChange B S hS f g f' g' sq.w
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
        (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
          ((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ)) :=
  ⟨fun E hE => geometricPointwiseBaseChange_tensor sq E K hE hK K' hK' φ h,
    fun E hE => geometricPointwiseBaseChange_sheafHom_of_isPerfect sq E hE K hK K' hK' φ h,
    fun hg hKb E hE => geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent sq hg E hE K
      ⟨hKb, hK⟩ K' hK' φ h⟩

end AlgebraicGeometry.Space

end
