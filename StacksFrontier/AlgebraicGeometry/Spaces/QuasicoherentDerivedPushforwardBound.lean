module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# A uniform upper bound for the derived direct image on `D_QCoh`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a scheme
`S` contained in a big fppf site `B`, with `Y` quasi-compact.  There is an integer `N` such that
for every morphism `Y' ⟶ Y`, with base change `f' : X' ⟶ Y'` of `f`, and every `E` in
`D_QCoh(𝒪_{X'})` with `H^m(E) = 0` for `m > 0`, we have `H^m(Rf'_*E) = 0` for `m ≥ N`
(Stacks 08FA, parts (2) and (3)).

## Main definitions

* `AlgebraicGeometry.Space.PushforwardRaisesBoundBy`: the direct image along a morphism carries
  a K-injective complex with quasi-coherent cohomology in degrees `≤ c` to a complex with
  cohomology in degrees `≤ c + N`.

## Main results

* `AlgebraicGeometry.Space.exists_pushforwardRaisesBoundBy_baseChange_of_isAffineSpace`: over an
  affine base, one bound for every base change, by the induction principle of Stacks 08GP.
* `AlgebraicGeometry.Space.exists_isZero_homology_derivedModulePushforward_baseChange`:
  **Stacks 08FA, part (3)**.
* `AlgebraicGeometry.Space.exists_isZero_homology_derivedModulePushforward`:
  **Stacks 08FA, part (2)**.

## Implementation notes

The source deduces the bound from Stacks 073G.  Here it is proved directly, along the lines of
the proof of part (1).  Over an affine base the property "one bound `N` serves every base change
of the morphism" is proved by the induction principle of Stacks 08GP: an affine source is affine
over the base, and so are its base changes, which therefore raise no bound; an elementary
distinguished square stays elementary distinguished after base change (Stacks 08GN), and the
Mayer–Vietoris triangle of Stacks 08GW turns bounds `N` on the two members and `N - 1` on their
intersection into the bound `N`.  For a quasi-compact base `Y` choose an affine surjective étale
`A ⟶ Y` (Stacks 03H6); a module on `Y'` vanishes when it vanishes on étale charts of `Y'` lying
over `A`, since these refine every étale chart of `Y'` by a surjective étale map, and over such a
chart the direct image is computed by a base change of `X ×_Y A ⟶ A` (Stacks 03LX).

## References

* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated
open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of modules along `g` carries every K-injective complex of `𝒪_W`-modules with
quasi-coherent cohomology sheaves vanishing above `c` to a complex whose cohomology sheaves
vanish above `c + N`. -/
def PushforwardRaisesBoundBy {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y) (N : ℤ) : Prop :=
  ∀ I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ, I.IsKInjective →
    (∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) → ∀ c : ℤ,
      (DerivedCategory.Q.obj I).IsLE c →
      (DerivedCategory.Q.obj (((modulePushforward B S hS g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)).IsLE (c + N)

variable {B S hS} in
/-- A bound may be enlarged. -/
theorem PushforwardRaisesBoundBy.mono {W Y : AlgebraicSpaces B S hS} {g : W ⟶ Y} {N M : ℤ}
    (h : PushforwardRaisesBoundBy B S hS g N) (hNM : N ≤ M) :
    PushforwardRaisesBoundBy B S hS g M := fun I hI hqc c hc => by
  have := h I hI hqc c hc
  exact DerivedCategory.TStructure.t.isLE_of_le _ (c + N) (c + M) (by omega)

/-- The direct image along an affine morphism raises no bound. -/
theorem pushforwardRaisesBoundBy_zero_of_isAffineHom {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y)
    (hg : IsAffineHom B S hS g.hom) : PushforwardRaisesBoundBy B S hS g 0 := by
  intro I hI hqc c hc
  rw [add_zero, DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff] at hc
  exact fun j hj => exactAt_modulePushforward_of_isAffineHom B S hS g hg I hI hqc c
    (fun q hq => (hc q hq).isZero_homology) j hj

/-- Restriction along an étale morphism keeps an upper bound of a complex: it is exact, so it
commutes with cohomology. -/
theorem isLE_Q_obj_etaleModulePullback {W Z : AlgebraicSpaces B S hS}
    (j : W ⟶ Z) (hj : IsEtale B S hS j.hom)
    (I : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) (c : ℤ)
    (hc : (DerivedCategory.Q.obj I).IsLE c) :
    (DerivedCategory.Q.obj (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)).IsLE c := by
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff] at hc ⊢
  intro q hq
  have h := hc q hq
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  exact (Functor.map_isZero (etaleModulePullback.{u, u} B S hS j hj) h).of_iso
    ((I.sc q).mapHomologyIso (etaleModulePullback.{u, u} B S hS j hj))

/-! ### The Mayer–Vietoris step -/

section MayerVietoris

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W Y : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- **The Mayer–Vietoris step.**  Let `(U ⊆ W, V → W)` be an elementary distinguished square and
`g : W ⟶ Y` a morphism.  If the direct images along `U ⟶ Y` and `V ⟶ Y` raise bounds by at most
`N`, and the direct image along `U ×_W V ⟶ Y` by at most `N - 1`, then the direct image along `g`
raises bounds by at most `N`. -/
theorem pushforwardRaisesBoundBy_of_isElementaryDistinguishedSquare (g : W ⟶ Y) (N : ℤ)
    (hU : PushforwardRaisesBoundBy B S hS (edsOpenHom B S hS hsq ≫ g) N)
    (hV : PushforwardRaisesBoundBy B S hS (edsEtaleHom B S hS hsq ≫ g) N)
    (hP : PushforwardRaisesBoundBy B S hS (edsInterHom B S hS hsq ≫ g) (N - 1)) :
    PushforwardRaisesBoundBy B S hS g N := by
  intro I hI hqc c hc
  obtain ⟨δ, hT⟩ := mem_distTriang_unitBiprod_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) I
  have := hasRightDerivedFunctor_modulePushforward B S hS g
  let RF := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  let α := ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  have hT' := RF.map_distinguished _ hT
  -- the three pieces of the square
  have key : ∀ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ W) (hj : IsEtale B S hS j.hom) (M : ℤ),
      PushforwardRaisesBoundBy B S hS (j ≫ g) M →
      (RF.obj (DerivedCategory.Q.obj
        (((etaleModulePullback.{u, u} B S hS j hj ⋙
          modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).IsLE
            (c + M) := by
    intro Z j hj M hZ
    let J := ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    have hJ : CochainComplex.IsKInjective J :=
      isKInjective_etaleModulePullback_of_isEtale B S hS j hj I hI
    let e₁ : ((etaleModulePullback.{u, u} B S hS j hj ⋙
        modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
        ((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j))
        (ComplexShape.up ℤ)).app I).symm
    have hK := isKInjective_modulePushforward_of_isEtale B S hS j hj J hJ
    obtain ⟨e₂⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α _ hK
    let e₃ : ((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≅
        ((modulePushforward B S hS (j ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
      (Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS j g)
        (ComplexShape.up ℤ)).app J
    have := hZ J hJ
      (fun q => isQuasicoherentOnSite_homology_etaleModulePullback B S hS j hj I hqc q)
      c (isLE_Q_obj_etaleModulePullback B S hS j hj I c hc)
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((RF.mapIso (DerivedCategory.Q.mapIso e₁) ≪≫ e₂ ≪≫ DerivedCategory.Q.mapIso e₃).symm) (c + M)
  have hb := DerivedCategory.TStructure.t.isLE₂
    (RF.mapTriangle.obj (binaryBiproductTriangle
      (DerivedCategory.Q.obj (((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))
      (DerivedCategory.Q.obj (((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))))
    (RF.map_distinguished _ (binaryBiproductTriangle_distinguished _ _)) (c + N)
    (key _ _ (isEtale_edsOpenHom B S hS hsq) N hU) (key _ _ (isEtale_edsEtaleHom B S hS hsq) N hV)
  have hP' := key _ _ (isEtale_edsInterHom B S hS hsq) (N - 1) hP
  have hshift : ∀ X : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      X.IsLE (c + (N - 1)) → (X⟦(-1 : ℤ)⟧).IsLE (c + N) := fun X hX => by
    have := hX
    exact DerivedCategory.TStructure.t.isLE_shift X (c + (N - 1)) (-1) (c + N) (by omega)
  have hA := DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang _ hT')
    (c + N) (hshift _ hP') hb
  obtain ⟨e⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α I hI
  have : (RF.obj (DerivedCategory.Q.obj I)).IsLE (c + N) := hA
  exact DerivedCategory.TStructure.t.isLE_of_iso e (c + N)

end MayerVietoris

/-! ### Base change of an elementary distinguished square -/

/-- Let `U' = U ×_W X'` and `V' = V ×_W X'` be the base changes of `U ⟶ W` and `V ⟶ W` along
`X' ⟶ W`.  Then `U' ×_{X'} V'` is the base change of `U ×_W V` along `X' ⟶ W`. -/
theorem exists_isPullback_inter_of_isPullback {C : Type*} [Category C]
    {W X' U V U' V' Z Z' : C} {jU : U ⟶ W} {jV : V ⟶ W} {i : X' ⟶ W}
    {a : U' ⟶ U} {jU' : U' ⟶ X'} {b : V' ⟶ V} {jV' : V' ⟶ X'}
    {p₁ : Z ⟶ U} {p₂ : Z ⟶ V} {p₁' : Z' ⟶ U'} {p₂' : Z' ⟶ V'}
    (S₁ : IsPullback a jU' jU i) (S₂ : IsPullback b jV' jV i)
    (S₃ : IsPullback p₁' p₂' jU' jV') (S₄ : IsPullback p₁ p₂ jU jV) :
    ∃ m : Z' ⟶ Z, IsPullback m (p₁' ≫ jU') (p₁ ≫ jU) i := by
  have H₁ := S₃.flip.paste_horiz S₂
  rw [← S₁.w] at H₁
  have hw : (p₂' ≫ b) ≫ jV = (p₁' ≫ a) ≫ jU := by
    rw [Category.assoc, Category.assoc, S₁.w, S₂.w, ← Category.assoc, ← Category.assoc, S₃.w]
  let m : Z' ⟶ Z := S₄.flip.lift (p₂' ≫ b) (p₁' ≫ a) hw
  have T₁ : IsPullback m p₁' p₁ a := by
    refine IsPullback.of_right ?_ (S₄.flip.lift_snd _ _ hw) S₄.flip
    rw [S₄.flip.lift_fst _ _ hw]
    exact H₁
  exact ⟨m, T₁.paste_vert S₁⟩

section BaseChange

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W A : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- **The Mayer–Vietoris step, uniformly in the base change.**  Let `(U ⊆ W, V → W)` be an
elementary distinguished square and `g : W ⟶ A`.  If every base change of `U ⟶ A` and of
`V ⟶ A` raises bounds by at most `N`, and every base change of `U ×_W V ⟶ A` by at most
`N - 1`, then every base change of `g` raises bounds by at most `N`.

The base change of the square along `X' ⟶ W` is elementary distinguished by Stacks 08GN, and its
three members are base changes of `U`, `V` and `U ×_W V`. -/
theorem pushforwardRaisesBoundBy_baseChange_of_isElementaryDistinguishedSquare (g : W ⟶ A)
    (N : ℤ)
    (hU : ∀ (T X' : AlgebraicSpaces B S hS) (h : T ⟶ A) (i : X' ⟶ edsOpen B S hS hsq)
      (f' : X' ⟶ T), IsPullback i f' (edsOpenHom B S hS hsq ≫ g) h →
        PushforwardRaisesBoundBy B S hS f' N)
    (hV : ∀ (T X' : AlgebraicSpaces B S hS) (h : T ⟶ A) (i : X' ⟶ edsEtale B S hS hsq)
      (f' : X' ⟶ T), IsPullback i f' (edsEtaleHom B S hS hsq ≫ g) h →
        PushforwardRaisesBoundBy B S hS f' N)
    (hP : ∀ (T X' : AlgebraicSpaces B S hS) (h : T ⟶ A) (i : X' ⟶ edsInter B S hS hsq)
      (f' : X' ⟶ T), IsPullback i f' (edsInterHom B S hS hsq ≫ g) h →
        PushforwardRaisesBoundBy B S hS f' (N - 1))
    (T X' : AlgebraicSpaces B S hS) (h : T ⟶ A) (i : X' ⟶ W) (f' : X' ⟶ T)
    (sq : IsPullback i f' g h) : PushforwardRaisesBoundBy B S hS f' N := by
  have hsq' := isElementaryDistinguishedSquare_preimage B S hS W.2 X'.2 Uo fV hsq i.hom
  have S₁ : IsPullback (ObjectProperty.homMk (Uo.fromPreimage i.hom) :
        edsOpen B S hS hsq' ⟶ edsOpen B S hS hsq)
      (edsOpenHom B S hS hsq') (edsOpenHom B S hS hsq) i :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) (Subfunctor.isPullback_preimage i.hom Uo)
  have S₂ : IsPullback (ObjectProperty.homMk (pullback.fst fV i.hom) :
        edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq)
      (edsEtaleHom B S hS hsq') (edsEtaleHom B S hS hsq) i :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) (IsPullback.of_hasPullback fV i.hom)
  obtain ⟨m, S₃⟩ := exists_isPullback_inter_of_isPullback S₁ S₂
    (isPullback_edsInter B S hS hsq') (isPullback_edsInter B S hS hsq)
  refine pushforwardRaisesBoundBy_of_isElementaryDistinguishedSquare B S hS hsq' f' N ?_ ?_ ?_
  · exact hU T _ h _ _ (by simpa only [Category.assoc] using S₁.paste_vert sq)
  · exact hV T _ h _ _ (by simpa only [Category.assoc] using S₂.paste_vert sq)
  · exact hP T _ h m _ (by simpa only [edsInterHom, Category.assoc] using S₃.paste_vert sq)

end BaseChange

/-! ### Over an affine base -/

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Over an affine base, one bound for every base change.**  If `X₀` is quasi-compact and
quasi-separated and `Y₀` is affine, there is an integer `N` such that for every morphism
`T ⟶ Y₀` of algebraic spaces the direct image along the base change `X₀ ×_{Y₀} T ⟶ T` of `f₀`
raises bounds by at most `N`.

This is the induction principle of Stacks 08GP: for an affine source the morphism and its base
changes are affine, and the bound passes across elementary distinguished squares by the
Mayer–Vietoris step. -/
theorem exists_pushforwardRaisesBoundBy_baseChange_of_isAffineSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) {X₀ Y₀ : AlgebraicSpaces B S hS} (f₀ : X₀ ⟶ Y₀)
    (hY₀ : IsAffineSpace B S hS Y₀.1) (hqc : IsQuasiCompactSpace B S hS X₀.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1) :
    ∃ N : ℤ, ∀ (T X' : AlgebraicSpaces B S hS) (h : T ⟶ Y₀) (i : X' ⟶ X₀) (f' : X' ⟶ T),
      IsPullback i f' f₀ h → PushforwardRaisesBoundBy B S hS f' N := by
  have key := qcqs_induction_on_self B S hS hZ X₀ hqc hqs
    (fun Z z => ∀ hZ' : IsAlgebraicSpace B S hS Z, ∃ N : ℤ,
      ∀ (T X' : AlgebraicSpaces B S hS) (h : T ⟶ Y₀)
        (i : X' ⟶ (⟨Z, hZ'⟩ : AlgebraicSpaces B S hS)) (f' : X' ⟶ T),
        IsPullback i f'
          ((ObjectProperty.homMk z : (⟨Z, hZ'⟩ : AlgebraicSpaces B S hS) ⟶ X₀) ≫ f₀) h →
        PushforwardRaisesBoundBy B S hS f' N)
    (fun V hV hV' => ⟨0, fun T X' h i f' sq =>
      pushforwardRaisesBoundBy_zero_of_isAffineHom B S hS f'
        (isAffineHom_of_isPullback' B S hS (AlgebraicSpaces.isPullback_hom B S hS sq)
          (isAffineHom_of_isAffineSpace B S hS _ hV hY₀))⟩)
    (fun W V U f hf hsq _ _ _ _ hPU hPV hPP hW' => by
      obtain ⟨NU, hNU⟩ := hPU hsq.isOpenSubspace.1
      obtain ⟨NV, hNV⟩ := hPV hsq.isAlgebraicSpace
      obtain ⟨NP, hNP⟩ := hPP (edsInter B S hS hsq).2
      refine ⟨max NU (max NV (NP + 1)), fun T X' h i f' sq => ?_⟩
      have step : ∀ {P Q : AlgebraicSpaces B S hS} {N₁ N₂ : ℤ} (φ : P ⟶ Q) c R,
          φ ≫ c = R → N₁ ≤ N₂ →
          (∀ T' X'' (h' : T' ⟶ Y₀) (i' : X'' ⟶ P) f'', IsPullback i' f'' R h' →
            PushforwardRaisesBoundBy B S hS f'' N₁) →
          ∀ T' X'' (h' : T' ⟶ Y₀) (i' : X'' ⟶ P) f'', IsPullback i' f'' (φ ≫ c) h' →
            PushforwardRaisesBoundBy B S hS f'' N₂ :=
        fun _ _ _ e hle hN T' X'' h' i' f'' sq' => (hN T' X'' h' i' f'' (e ▸ sq')).mono hle
      refine pushforwardRaisesBoundBy_baseChange_of_isElementaryDistinguishedSquare B S hS hsq
        _ _ ?_ ?_ ?_ T X' h i f' sq
      · exact step _ _ _ (ObjectProperty.hom_ext _ (by
          simp only [ObjectProperty.FullSubcategory.comp_hom]; rfl)) (by omega) hNU
      · exact step _ _ _ (ObjectProperty.hom_ext _ (by
          simp only [ObjectProperty.FullSubcategory.comp_hom, ← hf]; rfl)) (by omega) hNV
      · exact step _ _ _ (ObjectProperty.hom_ext _ (by
          simp only [ObjectProperty.FullSubcategory.comp_hom]; rfl)) (by omega) hNP)
  obtain ⟨N, hN⟩ := key X₀.2
  refine ⟨N, fun T X' h i f' sq => hN T X' h i f' ?_⟩
  have e : (ObjectProperty.homMk (𝟙 X₀.1) : X₀ ⟶ X₀) ≫ f₀ = f₀ :=
    ObjectProperty.hom_ext _ (by simp)
  rw [e]
  exact sq

/-! ### Étale localization on the base -/

/-- **The direct image restricted along an étale morphism of the base.**  For a cartesian square
with `g : Y' ⟶ Y` étale, the restriction to `Y'` of the cohomology of `f_*I` vanishes as soon as
the cohomology of `f'_*(I|_{X'})` does, the two being isomorphic by Stacks 03LX. -/
theorem isZero_etaleModulePullback_homology_modulePushforward
    {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (q : ℤ)
    (h : IsZero ((((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModulePullback.{u, u} B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).homology q)) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).obj
      ((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
        q)) := by
  have hi := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  let J := ((etaleModulePullback.{u, u} B S hS i hi).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  let HC := HomologicalComplex.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2)
    (ComplexShape.up ℤ) q
  let HH := HomotopyCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2)
    (ComplexShape.up ℤ) q
  let Qt := HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)
  let e₁ : HH.obj (((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (Qt.obj I)) ≅
      HC.obj (((etaleModulePullback.{u, u} B S hS g hg).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    HH.mapIso (((etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory
        (ComplexShape.up ℤ)).mapIso
          (((modulePushforward B S hS f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
        ((etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app _) ≪≫
      (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app _
  let e₂ : HH.obj (((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ)).obj (Qt.obj I)) ≅
      HC.obj (((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    HH.mapIso (((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ)).mapIso
          (((etaleModulePullback.{u, u} B S hS i hi).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).app I) ≪≫
        ((modulePushforward B S hS f').mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _) ≪≫
      (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app _
  let e₃ := HH.mapIso ((etaleModulePushforwardRestrictHomotopyIso B S hS sq hg).app (Qt.obj I))
  exact h.of_iso ((e₂.symm ≪≫ e₃.symm ≪≫ e₁) ≪≫
      (((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).sc
        q).mapHomologyIso (etaleModulePullback.{u, u} B S hS g hg))).symm

/-! ### A quasi-compact base -/

/-- **One bound for every base change of a quasi-compact quasi-separated morphism to a
quasi-compact base.**  There is an integer `N` such that for every morphism `Y' ⟶ Y` the direct
image along the base change `f' : X' ⟶ Y'` of `f` raises bounds by at most `N`.

Choose an affine surjective étale `A ⟶ Y` by Stacks 03H6, and the bound `N` of
`X ×_Y A ⟶ A` for all its base changes.  Every étale chart `V` of `Y'` is refined by the chart
`V ×_Y A`, surjective and étale over `V`; over it the direct image along `f'` is computed by a
base change of `X ×_Y A ⟶ A`, so the cohomology of the direct image vanishes on `V ×_Y A`, hence
on `V`, above `c + N`. -/
theorem exists_pushforwardRaisesBoundBy_baseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℤ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → PushforwardRaisesBoundBy B S hS f' N := by
  obtain ⟨U, a, hUaff, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).1 hY
  have hE := (isEtale_iff_presheaf_of_yoneda B S hS a).1 het
  let A : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a, hE⟩
  have hA : IsAffineChart B S hS Y.1 A := hUaff
  have hZ := B.contains_terminal
  obtain ⟨N, hN⟩ := exists_pushforwardRaisesBoundBy_baseChange_of_isAffineSpace B S hS hZ
    (chartBaseChangeProjection B S hS f A) (isAffineSpace_chartSpace B S hS Y A hA)
    (isQuasiCompactSpace_chartBaseChange B S hS f A hA hfqc)
    (isAbsolutelyQuasiSeparated_chartBaseChangeSpace B S hS hZ f A hA hfqs)
  refine ⟨N, fun Y' X' g g' f' sq' I hI hqc c hc => ?_⟩
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
  intro q hq
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine isZero_of_subsingleton_val_obj B S hS Y' _ fun V => ?_
  -- the chart `V ×_Y A` of `Y'` over `V`
  let γ := V.unop.1.hom ≫ g.hom
  let r := hsurj.rep
  have sqr := r.isPullback' γ
  have hqE : Etale ((BigFppfOver.toScheme B S hS).map (r.snd γ)) :=
    hE.property γ (yoneda.map (r.fst' γ)) (r.snd γ) sqr
  have hqS : Surjective ((BigFppfOver.toScheme B S hS).map (r.snd γ)) :=
    hsurj.property γ (yoneda.map (r.fst' γ)) (r.snd γ) sqr
  let W₀ : SmallEtale B S hS (chartSpace B S hS Y' V.unop).1 :=
    ⟨CostructuredArrow.mk (yoneda.map (r.snd γ)), (presheaf_yoneda_map_etale_iff B S hS _).2 hqE⟩
  let W := (smallEtalePostcomp B S hS (chartToSpace B S hS Y' V.unop)
    (isEtale_chartToSpace B S hS Y' V.unop)).obj W₀
  let k : W ⟶ V.unop := ObjectProperty.homMk (CostructuredArrow.homMk (r.snd γ) rfl)
  have hinj := injective_val_map_of_etale_surjective B S hS Y'
    ((((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q)
    k hqE hqS
  -- the base change of `X ×_Y A ⟶ A` to `W`
  let w : chartSpace B S hS Y' W ⟶ chartSpace B S hS Y A :=
    ObjectProperty.homMk (yoneda.map (r.fst' γ))
  have hw : chartToSpace B S hS Y' W ≫ g = w ≫ chartToSpace B S hS Y A :=
    ObjectProperty.hom_ext _ (by
      simp only [ObjectProperty.FullSubcategory.comp_hom]
      exact sqr.w.symm)
  have sqW := isPullback_chartBaseChangeInclusion B S hS f' W
  have sqA := isPullback_chartBaseChangeInclusion B S hS f A
  have hout : IsPullback (chartBaseChangeInclusion B S hS f' W ≫ g')
      (chartBaseChangeProjection B S hS f' W) f (w ≫ chartToSpace B S hS Y A) :=
    hw ▸ sqW.paste_horiz sq'
  have hmw := hout.w.trans (Category.assoc _ _ _).symm
  let m := sqA.lift _ _ hmw
  have sqm : IsPullback m (chartBaseChangeProjection B S hS f' W)
      (chartBaseChangeProjection B S hS f A) w := by
    refine IsPullback.of_right ?_ (sqA.lift_snd _ _ hmw) sqA
    rw [sqA.lift_fst _ _ hmw]
    exact hout
  have hb := hN _ _ w m _ sqm
  have hi := isEtale_chartBaseChangeInclusion B S hS f' W
  have hJ := isKInjective_etaleModulePullback_of_isEtale B S hS _ hi I hI
  have hJqc := isQuasicoherentOnSite_homology_etaleModulePullback B S hS _ hi I hqc
  have hJc := isLE_Q_obj_etaleModulePullback B S hS _ hi I c hc
  have hle := hb _ hJ hJqc c hJc
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff] at hle
  have hz := isZero_etaleModulePullback_homology_modulePushforward B S hS sqW
    (isEtale_chartToSpace B S hS Y' W) I q
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hle q hq))
  have hW := (isZero_etaleModulePullback_chartToSpace_iff B S hS Y' W _).1 hz W (𝟙 W)
  exact ⟨fun x y => hinj (hW.elim _ _)⟩

/-! ### Stacks 08FA, parts (2) and (3) -/

/-- **Stacks 08FA, part (3).**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism
of algebraic spaces over `S`, with `Y` quasi-compact.  There is an integer `N` such that for every
morphism of algebraic spaces `Y' ⟶ Y`, with base change `f' : X' ⟶ Y'` of `f`, and every `E` in
`D_QCoh(𝒪_{X'})` with `H^m(E) = 0` for `m > 0`, we have `H^m(Rf'_*E) = 0` for `m ≥ N`. -/
@[stacks 08FA "part (3)"]
theorem exists_isZero_homology_derivedModulePushforward_baseChange {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℤ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g →
      ∀ E : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2), QcohDerived B S hS X' E →
        (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj E)) →
        ∀ m : ℤ, N ≤ m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
          ((derivedModulePushforward B S hS f').obj E)) := by
  obtain ⟨N, hN⟩ := exists_pushforwardRaisesBoundBy_baseChange B S hS f hfqc hfqs hY
  refine ⟨N + 1, fun Y' X' g g' f' sq E hE hE0 m hm => ?_⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_modules B S hS E
  have hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite := by
    rw [← qcohDerived_Q_obj_iff]
    exact (QcohDerived B S hS X').prop_of_iso e hE
  have : E.IsLE 0 := (DerivedCategory.isLE_iff E 0).2 hE0
  have hc : (DerivedCategory.Q.obj I).IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e 0
  have hle := hN Y' X' g g' f' sq I hI hqc 0 hc
  obtain ⟨e'⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS f'
    (derivedModulePushforward B S hS f') (derivedModulePushforwardUnit B S hS f') I hI
  have : ((derivedModulePushforward B S hS f').obj E).IsLE (0 + N) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((derivedModulePushforward B S hS f').mapIso e ≪≫ e').symm (0 + N)
  exact ((derivedModulePushforward B S hS f').obj E).isZero_of_isLE (0 + N) m (by omega)

/-- **Stacks 08FA, part (2).**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism
of algebraic spaces over `S`, with `Y` quasi-compact.  There is an integer `N` such that for every
`E` in `D_QCoh(𝒪_X)` with `H^m(E) = 0` for `m > 0`, we have `H^m(Rf_*E) = 0` for `m ≥ N`. -/
@[stacks 08FA "part (2)"]
theorem exists_isZero_homology_derivedModulePushforward {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℤ, ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X E →
      (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj E)) →
      ∀ m : ℤ, N ≤ m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
        ((derivedModulePushforward B S hS f).obj E)) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedModulePushforward_baseChange B S hS f hfqc hfqs hY
  exact ⟨N, hN Y X (𝟙 Y) (𝟙 X) f (IsPullback.of_id_fst)⟩

end AlgebraicGeometry.Space

end
