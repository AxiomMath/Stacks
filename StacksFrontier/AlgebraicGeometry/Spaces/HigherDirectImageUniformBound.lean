module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# A base-change-uniform vanishing bound for the higher direct images

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S`, with `Y` quasi-compact.  [Stacks, Tag 073G] asserts that there is a single integer
`n(X → Y)`, depending on `f` alone, such that for *every* algebraic space `Y'`, *every* morphism
`Y' ⟶ Y` and *every* quasi-coherent module `𝓕'` on `X' = Y' ×_Y X` the higher direct images
`R^i f'_*𝓕'` vanish for `i ≥ n(X → Y)`.  The order of the quantifiers is the whole content: the
bound is chosen before the base change and before the coefficient module.

The proof has two steps.

1. **An affine base.**  If `Y` is affine then `X` is quasi-compact and quasi-separated, and the
   induction principle for such spaces, [Stacks, Tag 08GP], applies to the property of an
   algebraic space `W` étale over `X` that `W ⟶ Y` has a uniform bound.  An affine `W` maps to
   the affine `Y` by an affine morphism, every base change of which is affine, and the higher
   direct images of quasi-coherent modules along affine morphisms vanish [Stacks, Tag 073H]: the
   bound is `1`.  Across an elementary distinguished square `(U ⊆ W, V ⟶ W)` with intersection
   `P`, the relative Mayer–Vietoris sequence gives `R^{n+1}k'_*𝓕 = 0` from the vanishing of the
   higher direct images along the restrictions to `U`, `V` (degree `n + 1`) and `P` (degree
   `n`); and the square base changes to an elementary distinguished square [Stacks, Tag 08GN]
   whose members are the base changes of `U`, `V` and `P`.
2. **A quasi-compact base.**  Choose a surjective étale `V ⟶ Y` with `V` affine
   [Stacks, Tag 03H6] and let `N` be the bound of the base change `X_V ⟶ V`.  For a base change
   `f' : X' ⟶ Y'` of `f`, the restriction of `R^q f'_*𝓕'` along the surjective étale
   `Y'_V ⟶ Y'` is the higher direct image along `X'_V ⟶ Y'_V` [Stacks, Tag 03LX], a base change
   of `X_V ⟶ V`; so it vanishes for `q ≥ N`, and a surjective étale morphism detects the zero
   module.

## Main definitions

* `AlgebraicGeometry.Space.IsUniformHigherDirectImageBound`: `N` bounds the vanishing of the
  higher direct images of quasi-coherent modules along every base change of a morphism.

## Main results

* `CategoryTheory.Sheaf.isZero_obj_of_mem_of_forall_isZero`: a sheaf with zero sections over the
  members of a covering sieve has zero sections over its base.
* `AlgebraicGeometry.Space.isZero_of_isZero_etaleModulePullback_of_isSurjective`: a surjective
  étale morphism detects the zero module.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_succ_of_eds`: Mayer–Vietoris
  vanishing for the higher direct images along a morphism out of the base of an elementary
  distinguished square.
* `AlgebraicGeometry.Space.isUniformHigherDirectImageBound_of_eds`: uniform bounds pass across
  elementary distinguished squares.
* `AlgebraicGeometry.Space.exists_isUniformHigherDirectImageBound_of_isAffineSpace`: the case of
  an affine base.
* `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward_of_qcqs`:
  **[Stacks, Tag 073G]**.  Step (2) of the source's proof, the reduction of an arbitrary base
  to a scheme base, is
  `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward` of
  `StacksFrontier/AlgebraicGeometry/Spaces/UniformHigherDirectImageVanishing.lean`; it is not used
  here.

## Implementation notes

**The proof is not the source's.**  The source reduces to an affine base and an affine `Y'`,
identifies `R^if'_*𝓕'` through `H^i(X', 𝓕') = H^0(Y', R^if'_*𝓕')` ([Stacks, Tag 0720] and
[Stacks, Tag 0733]) and bounds `H^i(X', 𝓕')` by the choices of [Stacks, Tag 072C], which base
change.  Here the bound for the higher direct images themselves is propagated along the
induction principle of [Stacks, Tag 08GP], over an arbitrary base `Y'`; so neither the quotients
`U_p` of [Stacks, Tag 072C] nor the comparison with cohomology are needed, and the reduction
from an arbitrary base to an affine one disappears.

**Degrees.**  `R^i f'_*` is Mathlib's `CategoryTheory.Functor.rightDerived`, indexed by `ℕ`;
negative degrees do not occur, so an `ℕ`-indexed bound is the source's integer bound.  Vanishing
is the categorical predicate `IsZero`, and quasi-coherence is
`SheafOfModules.IsQuasicoherentOnSite`, that is [Stacks, Tag 03DL], part (6), on the small étale
site.  The base change `X' = Y' ×_Y X` is any algebraic space completing a cartesian square over
`f`, so the statement does not depend on a choice of fibre product.

## References

* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

/-! ### Sections over an object covered by objects with no sections -/

namespace CategoryTheory.Sheaf

/-- **A sheaf has a zero group of sections over an object covered by objects over which it has
zero sections.**  The zero family on a covering sieve has a unique amalgamation, and both the
identity and the zero endomorphism of the sections over the object amalgamate it. -/
theorem isZero_obj_of_mem_of_forall_isZero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Type*} [Category* A] [Preadditive A] (F : Sheaf J A)
    {V : C} {R : Sieve V} (hR : R ∈ J V)
    (h : ∀ ⦃W : C⦄ (g : W ⟶ V), R g → IsZero (F.obj.obj (Opposite.op W))) :
    IsZero (F.obj.obj (Opposite.op V)) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨_, -, hu⟩ := F.property (F.obj.obj (Opposite.op V)) R hR
    (fun W _ _ => (0 : F.obj.obj (Opposite.op V) ⟶ F.obj.obj (Opposite.op W))) (by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact (h (g₁ ≫ f₁) (R.downward_closed h₁ g₁)).eq_of_tgt _ _)
  exact (hu _ (by intro W g hg; exact (h g hg).eq_of_tgt _ _)).trans
    (hu _ (by intro W g hg; exact (h g hg).eq_of_tgt _ _)).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_HigherDirectImageUniformBound :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_HigherDirectImageUniformBound
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_HigherDirectImageUniformBound B S hS).has_limit _

/-! ### Detecting the zero module along a surjective étale morphism -/

/-- **A surjective étale morphism detects the zero module.**  If `c : Z ⟶ Y` is étale and
surjective and the restriction `c^*M` of an `𝒪_Y`-module `M` is zero, then `M` is zero.

Choose an étale scheme atlas `T ⟶ Z`.  The composite `T ⟶ Y` is a surjective étale chart of `Y`,
so it covers the final object of the small étale site; a chart lying over it factors through
`c`, so the sections of `M` over it are sections of `c^*M`, which vanish; and a sheaf whose
sections vanish on a covering sieve has zero sections. -/
theorem isZero_of_isZero_etaleModulePullback_of_isSurjective {Z Y : AlgebraicSpaces B S hS}
    (c : Z ⟶ Y) (hc : IsEtale B S hS c.hom) (hsurj : IsSurjective B S hS c.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : IsZero ((etaleModulePullback.{u, u} B S hS c hc).obj M)) : IsZero M := by
  obtain ⟨T, t, htsurj, htet⟩ := Z.2.exists_atlas
  have ht : IsEtale B S hS t := (isEtale_iff_presheaf_of_yoneda B S hS t).2 htet
  let U : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (t ≫ c.hom),
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS ht hc)⟩
  have hUsurj : IsSurjective B S hS U.1.hom :=
    isSurjective_comp B S hS ((presheafSurjective_iff_isSurjective_yoneda B S hS Z.1 Z.2 T t).1
      htsurj) hsurj
  have hcov := SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 U hUsurj
  rw [SheafOfModules.isZero_iff_forall_isZero_obj]
  intro W
  suffices hAb : IsZero (((SheafOfModules.toSheaf _).obj M).obj.obj (Opposite.op W)) from
    ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 hAb)
  refine CategoryTheory.Sheaf.isZero_obj_of_mem_of_forall_isZero
    ((SheafOfModules.toSheaf _).obj M) (hcov W) ?_
  rintro W' g ⟨_, ⟨φ⟩⟩
  have hW'' : IsEtale B S hS (yoneda.map φ.hom.left ≫ t) :=
    isEtale_of_presheaf_etale B S hS (etale_comp_of_scheme B S hS φ.hom.left t
      (etale_toScheme_toOver_map B S hS Y.1 φ) (presheaf_etale_of_isEtale B S hS ht))
  let W'' : SmallEtale B S hS Z.1 :=
    ⟨CostructuredArrow.mk (yoneda.map φ.hom.left ≫ t),
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 hW''⟩
  let e : (smallEtalePostcomp B S hS c hc).obj W'' ≅ W' :=
    ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ W'.1.hom = (yoneda.map φ.hom.left ≫ t) ≫ c.hom
      rw [Category.id_comp, Category.assoc, ← CostructuredArrow.w φ.hom]
      rfl))
  have h0 : IsZero (M.val.obj (Opposite.op ((smallEtalePostcomp B S hS c hc).obj W''))) :=
    (SheafOfModules.isZero_iff_forall_isZero_obj _ _).1 hM W''
  have : Subsingleton (M.val.obj (Opposite.op ((smallEtalePostcomp B S hS c hc).obj W''))) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (AddCommGrpCat.isZero_iff_subsingleton.2 this).of_iso (M.val.presheaf.mapIso e.op)

/-! ### Mayer–Vietoris vanishing for higher direct images -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {Z : AlgebraicSpaces B S hS} (h : W ⟶ Z)

/-- The right derived functors of `F ↦ h_*(j_{Y,*}(F|_Y))` are the higher direct images of
`F|_Y` along `j_Y ≫ h`, for an étale `j_Y : Y ⟶ W`: restriction along `j_Y` is exact and preserves
injectives, and `h_* ∘ j_{Y,*} = (j_Y ≫ h)_*`. -/
def rightDerivedRestrictPushPushforwardIso {Y : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom)
    (Φ : Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2) [Φ.Additive]
    (e : Φ ≅ etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS (j ≫ h))
    (F : Modules.{u, u} B S hS W.1 W.2) (n : ℕ) :
    (Φ.rightDerived n).obj F ≅
      ((modulePushforward B S hS (j ≫ h)).rightDerived n).obj
        ((etaleModulePullback.{u, u} B S hS j hj).obj F) :=
  have := preservesInjectiveObjects_etaleModulePullback B S hS j hj
  have := modulePushforward_additive B S hS (j ≫ h)
  (Functor.rightDerivedIsoOfNatIso e n).app F ≪≫
    Stacks.RightDerivedComp.objIso (etaleModulePullback.{u, u} B S hS j hj)
      (injectiveResolution F) (fun m hm => Functor.isZero_rightDerived_of_exact _ F m hm)
      (modulePushforward B S hS (j ≫ h)) n

/-- **Mayer–Vietoris vanishing for higher direct images.**  Let `(U ⊆ W, j_V : V ⟶ W)` be an
elementary distinguished square with intersection `P = U ×_W V`, let `h : W ⟶ Z` be a morphism of
algebraic spaces and let `F` be an `𝒪_W`-module.  Then `Rⁿ⁺¹h_*F = 0` as soon as the higher
direct images of the restrictions of `F` along the restrictions of `h` vanish: in degree `n + 1`
for `U` and `V`, and in degree `n` for `P`.

This is the relative Mayer–Vietoris sequence of [Stacks, Tag 08JK] read in one degree, obtained
from part (1) of [Stacks, Tag 08GW] by applying `h_*`. -/
theorem isZero_rightDerived_modulePushforward_succ_of_eds (F : Modules.{u, u} B S hS W.1 W.2)
    (n : ℕ)
    (hU : IsZero (((modulePushforward B S hS (edsOpenHom B S hS hsq ≫ h)).rightDerived
        (n + 1)).obj ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj F)))
    (hV : IsZero (((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ h)).rightDerived
        (n + 1)).obj ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj F)))
    (hP : IsZero (((modulePushforward B S hS (edsInterHom B S hS hsq ≫ h)).rightDerived
        n).obj ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F))) :
    IsZero (((modulePushforward B S hS h).rightDerived (n + 1)).obj F) := by
  have := modulePushforward_additive B S hS h
  have := modulePushforward_additive B S hS (edsOpenHom B S hS hsq)
  have := modulePushforward_additive B S hS (edsEtaleHom B S hS hsq)
  have := modulePushforward_additive B S hS (edsInterHom B S hS hsq)
  exact isZero_rightDerived_succ_of_natural_shortExact (edsAdjOpen B S hS hsq).unit
    (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (modulePushforward B S hS h) (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) F n
    (hU.of_iso (rightDerivedRestrictPushPushforwardIso B S hS h _ _ _
      (edsRestrictPushOpenPushforwardIso B S hS hsq h) F (n + 1)))
    (hV.of_iso (rightDerivedRestrictPushPushforwardIso B S hS h _ _ _
      (edsRestrictPushEtalePushforwardIso B S hS hsq h) F (n + 1)))
    (hP.of_iso (rightDerivedRestrictPushPushforwardIso B S hS h _ _ _
      (edsRestrictPushInterPushforwardIso B S hS hsq h) F n))

end Square

/-! ### Uniform bounds for the higher direct images -/

/-- `N` is a **uniform vanishing bound for the higher direct images** of `k : W ⟶ Y`: for every
base change `k' : W' ⟶ Y'` of `k` along a morphism `g : Y' ⟶ Y` of algebraic spaces and every
quasi-coherent `𝒪_{W'}`-module `F`, the higher direct images `R^q k'_*F` vanish for `q ≥ N`.

[Stacks, Tag 073G] is the existence of such a bound for a quasi-compact quasi-separated `k` with
quasi-compact target. -/
def IsUniformHigherDirectImageBound {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y) (N : ℕ) :
    Prop :=
  ∀ (Y' W' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i : W' ⟶ W) (k' : W' ⟶ Y'),
    IsPullback i k' k g → ∀ F : Modules.{u, u} B S hS W'.1 W'.2, F.IsQuasicoherentOnSite →
      ∀ q : ℕ, N ≤ q → IsZero (((modulePushforward B S hS k').rightDerived q).obj F)

namespace IsUniformHigherDirectImageBound

variable {B S hS}

/-- A uniform bound may be raised. -/
theorem mono {W Y : AlgebraicSpaces B S hS} {k : W ⟶ Y} {N M : ℕ}
    (h : IsUniformHigherDirectImageBound B S hS k N) (hNM : N ≤ M) :
    IsUniformHigherDirectImageBound B S hS k M :=
  fun Y' W' g i k' sq F hF q hq => h Y' W' g i k' sq F hF q (hNM.trans hq)

/-- A uniform bound for `k` is one for every base change of `k`: a base change of a base change
is a base change, by pasting the two cartesian squares. -/
theorem of_isPullback {W Y W₁ Y₁ : AlgebraicSpaces B S hS} {k : W ⟶ Y} {N : ℕ}
    (h : IsUniformHigherDirectImageBound B S hS k N) {i₁ : W₁ ⟶ W} {k₁ : W₁ ⟶ Y₁}
    {g₁ : Y₁ ⟶ Y} (sq₁ : IsPullback i₁ k₁ k g₁) :
    IsUniformHigherDirectImageBound B S hS k₁ N :=
  fun Y' W' g i k' sq F hF q hq => h Y' W' (g ≫ g₁) (i ≫ i₁) k' (sq.paste_horiz sq₁) F hF q hq

end IsUniformHigherDirectImageBound

/-- **An affine morphism has the uniform bound `1`**: its base changes are affine, and the higher
direct images of a quasi-coherent module along an affine morphism vanish
([Stacks, Tag 073H]). -/
theorem isUniformHigherDirectImageBound_one_of_isAffineHom {W Y : AlgebraicSpaces B S hS}
    (k : W ⟶ Y) (hk : IsAffineHom B S hS k.hom) : IsUniformHigherDirectImageBound B S hS k 1 :=
  fun _ _ _ _ k' sq F hF q hq =>
    isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS k'
      (isAffineHom_of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hk) F hF q
      (by omega)

/-- **A uniform bound across an elementary distinguished square.**  Let `(U ⊆ W, j_V : V ⟶ W)` be
an elementary distinguished square with intersection `P = U ×_W V` and let `k : W ⟶ Y`.  If the
restrictions of `k` to `U`, `V` and `P` have uniform bounds `N_U`, `N_V` and `N_P`, then
`max (N_U, N_V, N_P + 1, 1)` is a uniform bound for `k`.

A base change of `k` along `Y' ⟶ Y` is a morphism `k' : W' ⟶ Y'` together with `W' ⟶ W`; the
square base changes to an elementary distinguished square on `W'` ([Stacks, Tag 08GN]) whose
three members are the base changes of `U`, `V` and `P`, so the relative Mayer–Vietoris vanishing
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_succ_of_eds` applies to `k'`. -/
theorem isUniformHigherDirectImageBound_of_eds {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {Y : AlgebraicSpaces B S hS}
    (k : W ⟶ Y) {NU NV NP : ℕ}
    (hU : IsUniformHigherDirectImageBound B S hS (edsOpenHom B S hS hsq ≫ k) NU)
    (hV : IsUniformHigherDirectImageBound B S hS (edsEtaleHom B S hS hsq ≫ k) NV)
    (hP : IsUniformHigherDirectImageBound B S hS (edsInterHom B S hS hsq ≫ k) NP) :
    IsUniformHigherDirectImageBound B S hS k (max (max (max NU NV) (NP + 1)) 1) := by
  intro Y' W' g i k' sq F hF q hq
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have hsq' := isElementaryDistinguishedSquare_preimage B S hS W.2 W'.2 Uo fV hsq i.hom
  -- The three members of the base-changed square are base changes of the three members.
  let iU : edsOpen B S hS hsq' ⟶ edsOpen B S hS hsq := ObjectProperty.homMk (Uo.fromPreimage i.hom)
  have sqU : IsPullback iU (edsOpenHom B S hS hsq') (edsOpenHom B S hS hsq) i :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
      (Subfunctor.isPullback_preimage i.hom Uo)
  let iV : edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq :=
    ObjectProperty.homMk (pullback.fst fV i.hom)
  have sqV : IsPullback iV (edsEtaleHom B S hS hsq') (edsEtaleHom B S hS hsq) i :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (IsPullback.of_hasPullback fV i.hom)
  have A := isPullback_edsInter B S hS hsq
  have A' := isPullback_edsInter B S hS hsq'
  let iP : edsInter B S hS hsq' ⟶ edsInter B S hS hsq :=
    A.lift (edsFst B S hS hsq' ≫ iU) (edsSnd B S hS hsq' ≫ iV) (by
      rw [Category.assoc, Category.assoc, sqU.w, sqV.w, ← Category.assoc, ← Category.assoc, A'.w])
  have hPs : iP ≫ edsSnd B S hS hsq = edsSnd B S hS hsq' ≫ iV := A.lift_snd _ _ _
  have hPf : iP ≫ edsFst B S hS hsq = edsFst B S hS hsq' ≫ iU := A.lift_fst _ _ _
  have big : IsPullback (iP ≫ edsSnd B S hS hsq) (edsFst B S hS hsq') (edsEtaleHom B S hS hsq)
      (iU ≫ edsOpenHom B S hS hsq) := by
    rw [hPs]
    convert A'.flip.paste_horiz sqV using 1
    exact sqU.w
  have D : IsPullback iP (edsFst B S hS hsq') (edsFst B S hS hsq) iU :=
    IsPullback.of_right big hPf A.flip
  have sqP : IsPullback iP (edsInterHom B S hS hsq') (edsInterHom B S hS hsq) i :=
    D.paste_vert sqU
  refine isZero_rightDerived_modulePushforward_succ_of_eds B S hS hsq' k' F n ?_ ?_ ?_
  · exact hU Y' _ g iU _ (sqU.paste_vert sq) _
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ F hF) (n + 1) (by omega)
  · exact hV Y' _ g iV _ (sqV.paste_vert sq) _
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ F hF) (n + 1) (by omega)
  · exact hP Y' _ g iP _ (sqP.paste_vert sq) _
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ F hF) n (by omega)

/-! ### The uniform bound over an affine base -/

/-- **The source of a quasi-compact morphism to a quasi-compact algebraic space is
quasi-compact**: it is the base change of the morphism along the identity of the target. -/
theorem isQuasiCompactSpace_of_isQuasiCompact {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f) : IsQuasiCompactSpace B S hS X := by
  have : IsIso (pullback.snd (𝟙 Y) f) := (IsPullback.of_hasPullback (𝟙 Y) f).flip.isIso_fst_of_isIso
  exact IsQuasiCompactSpace.of_iso B S hS (hf Y hY hYqc (𝟙 Y)) (asIso (pullback.snd (𝟙 Y) f))

/-- **[Stacks, Tag 073G] over an affine base.**  A quasi-compact quasi-separated morphism
`f : X ⟶ Y` to an affine algebraic space has a uniform vanishing bound for its higher direct
images.

`X` is quasi-compact and quasi-separated, so the induction principle of [Stacks, Tag 08GP]
applies to the property of an algebraic space `W` étale over `X` that `W ⟶ X ⟶ Y` has a uniform
bound.  It holds when `W` is affine, `W ⟶ Y` being then a morphism of affine spaces, hence affine
(`AlgebraicGeometry.Space.isUniformHigherDirectImageBound_one_of_isAffineHom`), and it passes
across elementary distinguished squares
(`AlgebraicGeometry.Space.isUniformHigherDirectImageBound_of_eds`). -/
theorem exists_isUniformHigherDirectImageBound_of_isAffineSpace {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) : ∃ N, IsUniformHigherDirectImageBound B S hS f N := by
  have hZ := B.contains_terminal
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hfqs
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 (IsAffineSpace.isQuasiCompactSpace hY) f.hom
      hfqc
  obtain ⟨N, hN⟩ := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Wp s => ∀ hW : IsAlgebraicSpace B S hS Wp, ∃ N : ℕ,
      IsUniformHigherDirectImageBound B S hS
        (ObjectProperty.homMk (s ≫ f.hom) : (⟨Wp, hW⟩ : AlgebraicSpaces B S hS) ⟶ Y) N)
    (fun V hVaff hW => ⟨1, isUniformHigherDirectImageBound_one_of_isAffineHom B S hS _
      (isAffineHom_of_isAffineSpace B S hS _ hVaff hY)⟩)
    (by
      intro W V U fv hfv hsq _ _ _ _ hPU hPV hPP hW
      let kW : W.1.left ⟶ Y := ObjectProperty.homMk (W.1.hom.hom ≫ f.hom)
      obtain ⟨NU, hNU⟩ := hPU (edsOpen B S hS hsq).2
      obtain ⟨NV, hNV⟩ := hPV (edsEtale B S hS hsq).2
      obtain ⟨NP, hNP⟩ := hPP (edsInter B S hS hsq).2
      have key : ∀ {T : AlgebraicSpaces B S hS} (a : T ⟶ W.1.left) (m : T ⟶ Y) {N : ℕ},
          m.hom = a.hom ≫ kW.hom → IsUniformHigherDirectImageBound B S hS m N →
          IsUniformHigherDirectImageBound B S hS (a ≫ kW) N :=
        by
        rintro T a m N h hm
        rwa [← (ObjectProperty.hom_ext _ h : m = a ≫ kW)]
      have hNU' := key (edsOpenHom B S hS hsq) _ (Category.assoc _ _ _) hNU
      have hNV' := key (edsEtaleHom B S hS hsq) _ (by
        change V.1.hom.hom ≫ f.hom = fv ≫ W.1.hom.hom ≫ f.hom
        rw [← hfv, Category.assoc]) hNV
      have hNP' := key (edsInterHom B S hS hsq) _ (Category.assoc _ _ _) hNP
      exact ⟨_, isUniformHigherDirectImageBound_of_eds B S hS hsq kW hNU' hNV' hNP'⟩) X.2
  refine ⟨N, ?_⟩
  have e : (ObjectProperty.homMk (𝟙 X.1 ≫ f.hom) : (⟨X.1, X.2⟩ : AlgebraicSpaces B S hS) ⟶ Y) =
      f := ObjectProperty.hom_ext _ (Category.id_comp _)
  rwa [e] at hN

/-! ### Stacks 073G -/

/-- **A uniform bound over a quasi-compact base.**  A quasi-compact quasi-separated morphism
`f : X ⟶ Y` to a quasi-compact algebraic space has a uniform vanishing bound for its higher
direct images.

Choose a surjective étale morphism `v : V ⟶ Y` from an affine scheme ([Stacks, Tag 03H6]); the
base change `f_V : X_V ⟶ V` has a uniform bound `N` by
`AlgebraicGeometry.Space.exists_isUniformHigherDirectImageBound_of_isAffineSpace`.  For a base
change `f' : X' ⟶ Y'` of `f`, the restriction of `R^q f'_*F'` along the surjective étale
`Y'_V = Y' ×_Y V ⟶ Y'` is the higher direct image along `X'_V ⟶ Y'_V` ([Stacks, Tag 03LX]),
which is a base change of `f_V`, so it vanishes for `q ≥ N`; and a surjective étale morphism
detects the zero module
(`AlgebraicGeometry.Space.isZero_of_isZero_etaleModulePullback_of_isSurjective`). -/
theorem exists_isUniformHigherDirectImageBound {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) : ∃ N, IsUniformHigherDirectImageBound B S hS f N := by
  obtain ⟨V, v, hVaff, hvsurj, hvet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).1 hYqc
  let vA : representedAlgebraicSpace B S hS V ⟶ Y := ObjectProperty.homMk v
  have hvA : IsEtale B S hS vA.hom := hvet
  have hvAs : IsSurjective B S hS vA.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 V v).1 hvsurj
  have sqV := IsPullback.of_hasPullback f vA
  obtain ⟨N, hN⟩ := exists_isUniformHigherDirectImageBound_of_isAffineSpace B S hS
    (pullback.snd f vA)
    (isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sqV) hfqc)
    (isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sqV) hfqs)
    (isAffineSpace_yoneda B S hS V hVaff)
  refine ⟨N, fun Y' X' g i' f' sq F hF q hq => ?_⟩
  have sqY := IsPullback.of_hasPullback g vA
  have hc : IsEtale B S hS (pullback.fst g vA).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sqY.flip hvA
  have hcs : IsSurjective B S hS (pullback.fst g vA).hom :=
    isSurjective_of_isPullback B S hS sqY.flip hvAs
  have sqX := IsPullback.of_hasPullback f' (pullback.fst g vA)
  have ha : IsEtale B S hS (pullback.fst f' (pullback.fst g vA)).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sqX.flip hc
  have big := sqX.paste_horiz sq
  let k := sqV.lift (pullback.fst f' (pullback.fst g vA) ≫ i')
    (pullback.snd f' (pullback.fst g vA) ≫ pullback.snd g vA)
    (by rw [big.w, sqY.w, Category.assoc])
  have hkf : k ≫ pullback.fst f vA = pullback.fst f' (pullback.fst g vA) ≫ i' :=
    sqV.lift_fst _ _ _
  have hks : k ≫ pullback.snd f vA = pullback.snd f' (pullback.fst g vA) ≫ pullback.snd g vA :=
    sqV.lift_snd _ _ _
  have hk : IsPullback k (pullback.snd f' (pullback.fst g vA)) (pullback.snd f vA)
      (pullback.snd g vA) := by
    refine IsPullback.of_right ?_ hks sqV
    rw [hkf, ← sqY.w]
    exact big
  have hz := hN _ _ (pullback.snd g vA) k _ hk _
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ ha F hF) q hq
  exact isZero_of_isZero_etaleModulePullback_of_isSurjective B S hS _ hc hcs _
    (hz.of_iso ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS _ _ _ _
      sqX hc (preservesInjectiveObjects_etaleModulePullback B S hS _ _) q).app F).symm)

/-- **[Stacks, Tag 073G].**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over `S`, with `Y` quasi-compact.  There is a single degree `n(X → Y)` such that
for every algebraic space `Y'`, every morphism `Y' ⟶ Y`, every algebraic space `X'` making
`X' ⟶ X`, `X' ⟶ Y'` a cartesian square over `f`, and every quasi-coherent `𝒪_{X'}`-module `𝓕'`,
the higher direct images `R^q f'_*𝓕'` vanish for `q ≥ n(X → Y)`. -/
@[stacks 073G "n(X -> Y) is a natural number, chosen before the base change, the module and \
the degree; X' is any algebraic space completing a cartesian square over f"]
theorem exists_forall_isZero_rightDerived_modulePushforward_of_qcqs {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℕ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback i' f' f g →
      ∀ F' : Modules.{u, u} B S hS X'.1 X'.2, F'.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        IsZero (((modulePushforward B S hS f').rightDerived q).obj F') :=
  exists_isUniformHigherDirectImageBound B S hS f hfqc hfqs hYqc

end AlgebraicGeometry.Space

end
