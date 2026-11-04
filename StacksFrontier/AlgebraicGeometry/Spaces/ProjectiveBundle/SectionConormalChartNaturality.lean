module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointsAlgebraicSpace

/-!
# Naturality of the conormal module of a section at étale scheme points

Let `σ` be a section of the projective bundle `π : 𝐏(ℰ) ⟶ X` and let `x : T ⟶ X` be an étale
scheme point.  `AlgebraicGeometry.Space.sectionConormalChartIso` identifies `x^*𝒞_σ` with the
conormal module of the section `k_x : T ⟶ 𝐏(ℰ)_T` of the fibre, by Stacks 09RR along the
cartesian square of `k_x`.  This file proves that these identifications are natural along a
morphism `h : T' ⟶ T` of test objects: the base-change comparison `𝐏(ℰ)_{T'} ⟶ 𝐏(ℰ)_T` of the
fibres (`RelativeProjPoints.fibreComparison`, Stacks 084B) carries `k_{x ∘ h}` to `k_x`, the square
it forms with `h` is cartesian, and Stacks 09RR along the stacked squares pastes.

The pasting is proved once for arbitrary cartesian squares with étale lower edges.  The square
comparisons of inverse images paste by the coherence of Stacks 03LU, and the identifications of
étale restrictions of kernel ideal sheaves compose by the compatibility of Stacks 03LU with the
étale restriction of Stacks 03LW, the equalities of kernel ideal sheaves composing to the one of
the outer rectangle.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafZPowEtaleRestrictionIso`: the factor
  `φ^*(𝓘_iⁿ) ≅ 𝓘_{i_U}ⁿ` of Stacks 09RR before the inverse image along `i_U`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSquareCompIso_paste`: the square comparisons of two
  stacked commutative squares paste.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowEtaleRestrictionIso_comp`: the étale restriction
  of the powers of the kernel ideal sheaf along a composite.
* `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_comp`: Stacks 09RR is
  compatible with pasting cartesian squares.
* `AlgebraicGeometry.Space.sectionFibreLift_comp_fibreComparison`,
  `AlgebraicGeometry.Space.isPullback_sectionFibreLift_fibreComparison`,
  `AlgebraicGeometry.Space.isEtale_fibreComparison`: the square of sections over `h`.
* `AlgebraicGeometry.Space.sectionConormalChartIso_naturality`: the naturality of
  `AlgebraicGeometry.Space.sectionConormalChartIso`.

## Implementation notes

The statements fix the implicit objects of every `Functor.map` and `NatTrans.app` of an inverse
image of modules: two such terms that differ only in a definitionally equal spelling of those
objects (`(F ⋙ G).obj M` against `G.obj (F.obj M)`, or a piece of the conormal algebra against the
inverse image of a power of the kernel ideal sheaf) are not accepted by the kernel at the default
budget.  Where two spellings meet, the passage is made propositionally, through transports along
equalities of objects (`app_retype`, `map_retype`) that are identities definitionally.

## References

* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Whiskering cancels a composite `α ≫ β = 𝟙`. -/
private theorem whiskerLeft_comp_whiskerLeft_assoc_of_comp_eq_id {C D E : Type*} [Category C]
    [Category D] [Category E] (F : C ⥤ D) {G H : D ⥤ E} {α : H ⟶ G} {β : G ⟶ H}
    (hαβ : α ≫ β = 𝟙 H) {T : C ⥤ E} (h : F ⋙ H ⟶ T) :
    Functor.whiskerLeft F α ≫ Functor.whiskerLeft F β ≫ h = h := by
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, hαβ, Functor.whiskerLeft_id',
    Category.id_comp]

/-- A component of a natural transformation at an object, read at an equal object through the
transports along the equality. -/
theorem app_retype {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {X₁ X₂ : C} (e : X₁ = X₂) :
    α.app X₁ = eqToHom (congrArg F.obj e) ≫ α.app X₂ ≫ eqToHom (congrArg G.obj e.symm) := by
  subst e
  simp

/-- The image of a morphism under a functor, read between equal objects through the transports
along the equalities. -/
theorem map_retype {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} (eX : X₁ = X₂) (eY : Y₁ = Y₂) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hf : f₁ = eqToHom eX ≫ f₂ ≫ eqToHom eY.symm) :
    F.map f₁ = eqToHom (congrArg F.obj eX) ≫ F.map f₂ ≫ eqToHom (congrArg F.obj eY.symm) := by
  subst eX eY hf
  simp

section Pasting

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U X Z ZU : AlgebraicSpaces B S hS}

/-- The square comparison of `AlgebraicGeometry.Space.modulePullbackSquareCompIso`, written
out. -/
theorem modulePullbackSquareCompIso_hom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom =
      (modulePullbackCompIso B S hS p i).hom ≫
        eqToHom (congrArg (fun k : ZU ⟶ X => modulePullback B S hS k) hsq.symm) ≫
        (modulePullbackCompIso B S hS iU φ).inv := by
  rw [modulePullbackSquareCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]

variable {Z₁ U₁ Z₂ U₂ : AlgebraicSpaces B S hS}

/-- **The square comparisons of two horizontally stacked squares paste.**  For commutative
squares `i_{U₁} ≫ φ₁ = p₁ ≫ i` and `i_{U₂} ≫ φ₂ = p₂ ≫ i_{U₁}`, the comparison of the outer
rectangle, read through the composition comparisons of `p₂ ≫ p₁` and `φ₂ ≫ φ₁`, is the
comparison of the first square followed by that of the second. -/
theorem modulePullbackSquareCompIso_paste (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z) (iU₁ : Z₁ ⟶ U₁)
    (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) :
    (modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂).hom ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS φ₂ φ₁).inv
          (modulePullback B S hS iU₂) =
      Functor.whiskerLeft (modulePullback B S hS i) (modulePullbackCompIso B S hS p₂ p₁).inv ≫
        Functor.whiskerRight (modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ h₁).hom
          (modulePullback B S hS p₂) ≫
        Functor.whiskerLeft (modulePullback B S hS φ₁)
          (modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂).hom := by
  rw [modulePullbackSquareCompIso_hom, modulePullbackSquareCompIso_hom,
    modulePullbackSquareCompIso_hom, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  conv_lhs => rw [← modulePullbackCompIso_assoc_inv B S hS iU₂ φ₂ φ₁]
  conv_rhs =>
    rw [modulePullbackCompIso_inv_comp_whiskerRight_hom_assoc B S hS p₂ p₁ i,
      modulePullbackCompIso_inv_eqToHom_right_assoc B S hS p₂ h₁.symm]
    enter [2, 2]
    rw [← modulePullbackCompIso_assoc_inv_assoc B S hS p₂ iU₁ φ₁]
    enter [2]
    rw [whiskerLeft_comp_whiskerLeft_assoc_of_comp_eq_id _ (Iso.inv_hom_id _)]
  conv_rhs =>
    enter [2, 2]
    rw [modulePullbackCompIso_inv_eqToHom_left_assoc B S hS h₂.symm φ₁]
  conv_rhs =>
    enter [2]
    rw [eqToHom_trans_assoc]

/-- **The pasting of the two square comparisons, at a module.** -/
theorem modulePullbackSquareCompIso_paste_app (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z) (iU₁ : Z₁ ⟶ U₁)
    (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app ((modulePullback B S hS i).obj M) ≫
        ((modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂).app M).hom ≫
        (modulePullback B S hS iU₂).map ((modulePullbackCompIso B S hS φ₂ φ₁).inv.app M) =
      (modulePullback B S hS p₂).map
          ((modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ h₁).app M).hom ≫
        (modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂).hom.app
          ((modulePullback B S hS φ₁).obj M) := by
  have h := NatTrans.congr_app
    (modulePullbackSquareCompIso_paste B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [Iso.app_hom, Iso.app_hom, h, Iso.hom_inv_id_app_assoc]

/-- The pasting of the square comparisons, followed by comparisons out of the étale
restrictions that compose along `φ₂ ≫ φ₁`. -/
theorem modulePullbackSquareCompIso_paste_comp (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z) (iU₁ : Z₁ ⟶ U₁)
    (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (M : Modules.{u, u} B S hS X.1 X.2)
    (N₁ : Modules.{u, u} B S hS U₁.1 U₁.2) (N₂ : Modules.{u, u} B S hS U₂.1 U₂.2)
    (θ₁ : (modulePullback B S hS φ₁).obj M ⟶ N₁) (θ₂ : (modulePullback B S hS φ₂).obj N₁ ⟶ N₂)
    (θ₁₂ : (modulePullback B S hS (φ₂ ≫ φ₁)).obj M ⟶ N₂)
    (hθ : θ₁₂ = (modulePullbackCompIso B S hS φ₂ φ₁).inv.app M ≫
      (modulePullback B S hS φ₂).map θ₁ ≫ θ₂) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app ((modulePullback B S hS i).obj M) ≫
        ((modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂).app M).hom ≫
        (modulePullback B S hS iU₂).map θ₁₂ =
      (modulePullback B S hS p₂).map
          (((modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ h₁).app M).hom ≫
            (modulePullback B S hS iU₁).map θ₁) ≫
        ((modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂).app N₁).hom ≫
        (modulePullback B S hS iU₂).map θ₂ := by
  subst hθ
  have nat := (modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂).hom.naturality θ₁
  simp only [Functor.comp_map] at nat
  rewrite [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.app_hom (modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂) N₁, reassoc_of% nat]
  conv_lhs =>
    enter [2]
    rw [← Category.assoc]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  exact congrArg (· ≫ _)
    (modulePullbackSquareCompIso_paste_app B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂ M)


/-! ### The étale restriction of the kernel ideal sheaf -/

/-- **The étale restriction of the powers of the kernel ideal sheaf**: for a cartesian square
`i_U ≫ φ = p ≫ i` with `φ` étale, the identification `φ^*(𝓘_iⁿ) ≅ 𝓘_{i_U}ⁿ` of Stacks 03LW
followed by the equality of `AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq`.
This is the factor of `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso` read
before the inverse image along `i_U`. -/
def kernelIdealSheafZPowEtaleRestrictionIso (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (modulePullback B S hS φ).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≅
      (kernelIdealSheafZPow B S hS iU n).toSheafOfModules :=
  (modulePullbackIsoEtaleModulePullback B S hS φ hφ).app _ ≪≫
    eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)

/-- Stacks 09RR in degree `n`, with its three factors named. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_eq_trans (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X) (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n =
      (modulePullbackSquareCompIso B S hS p iU i φ sq.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≪≫
        (modulePullback B S hS iU).mapIso
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≪≫
        (modulePullback B S hS iU).mapIso
          (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)) :=
  rfl

/-- Stacks 09RR in degree `n` is the square comparison followed by the inverse image along `i_U`
of `AlgebraicGeometry.Space.kernelIdealSheafZPowEtaleRestrictionIso`. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_hom_eq_squareCompIso_comp (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n).hom =
      ((modulePullbackSquareCompIso B S hS p iU i φ sq.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU).map
          (kernelIdealSheafZPowEtaleRestrictionIso B S hS p iU i φ sq hφ n).hom :=
  (congrArg Iso.hom
      (conormalAlgebraEtaleRestrictionPieceIso_eq_trans B S hS p iU i φ sq hφ n)).trans
    (congrArg (fun e => (((modulePullbackSquareCompIso B S hS p iU i φ sq.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≪≫ e).hom)
      ((modulePullback B S hS iU).mapIso_trans
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
        (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n))).symm)

/-- **The identification of Stacks 03LW along a composite**, followed by identifications of the
étale restrictions with given modules: it is the identification along the two factors in turn,
read through the composition comparison of Stacks 03LU. -/
theorem modulePullbackIsoEtaleModulePullback_comp_eqToHom (φ₁ : U₁ ⟶ X) (φ₂ : U₂ ⟶ U₁)
    (hφ₁ : IsEtale B S hS φ₁.hom) (hφ₂ : IsEtale B S hS φ₂.hom)
    (hφ₁₂ : IsEtale B S hS (φ₂ ≫ φ₁).hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (N₁ : Modules.{u, u} B S hS U₁.1 U₁.2) (N₂ : Modules.{u, u} B S hS U₂.1 U₂.2)
    (e₁ : (etaleModulePullback.{u, u} B S hS φ₁ hφ₁).obj M = N₁)
    (e₂ : (etaleModulePullback.{u, u} B S hS φ₂ hφ₂).obj N₁ = N₂)
    (e₁₂ : (etaleModulePullback.{u, u} B S hS (φ₂ ≫ φ₁) hφ₁₂).obj M = N₂) :
    (modulePullbackIsoEtaleModulePullback B S hS (φ₂ ≫ φ₁) hφ₁₂).hom.app M ≫ eqToHom e₁₂ =
      (modulePullbackCompIso B S hS φ₂ φ₁).inv.app M ≫
        (modulePullback B S hS φ₂).map
          ((modulePullbackIsoEtaleModulePullback B S hS φ₁ hφ₁).hom.app M ≫ eqToHom e₁) ≫
        (modulePullbackIsoEtaleModulePullback B S hS φ₂ hφ₂).hom.app N₁ ≫ eqToHom e₂ := by
  subst e₁ e₂
  have K := NatTrans.congr_app (modulePullbackCompIso_hom_comp_etaleRestriction B S hS φ₂ φ₁
    hφ₂ hφ₁ hφ₁₂ (etaleModulePullbackCompAdjunction_unit B S hS φ₂ φ₁ hφ₂ hφ₁ hφ₁₂)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at K
  have K₂ := (Iso.eq_comp_inv ((etaleModulePullbackComp B S hS φ₂ φ₁ hφ₂ hφ₁ hφ₁₂).app M)).mpr
    ((Category.assoc _ _ _).trans K.symm)
  simp only [Iso.app_inv] at K₂
  simp only [eqToHom_refl, Category.comp_id]
  rw [(modulePullbackIsoEtaleModulePullback B S hS φ₂ hφ₂).hom.naturality, K₂,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- **The étale restriction of the kernel ideal sheaf along a composite** is the restriction along
the two factors in turn, read through the composition comparison of Stacks 03LU. -/
theorem kernelIdealSheafZPowEtaleRestrictionIso_comp (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (sq₁ : IsPullback p₁ iU₁ i φ₁) (hφ₁ : IsEtale B S hS φ₁.hom)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁) (sq₂ : IsPullback p₂ iU₂ iU₁ φ₂)
    (hφ₂ : IsEtale B S hS φ₂.hom) (sq₁₂ : IsPullback (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁))
    (hφ₁₂ : IsEtale B S hS (φ₂ ≫ φ₁).hom) (n : ℤ) :
    (kernelIdealSheafZPowEtaleRestrictionIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n).hom =
      (modulePullbackCompIso B S hS φ₂ φ₁).inv.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        (modulePullback B S hS φ₂).map
          (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom :=
  modulePullbackIsoEtaleModulePullback_comp_eqToHom B S hS φ₁ φ₂ hφ₁ hφ₂ hφ₁₂ _ _ _
    (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n)
    (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n)
    (etaleModulePullback_kernelIdealSheafZPow_eq B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n)

/-- **Stacks 09RR is compatible with pasting cartesian squares**, with the degree-`n` pieces
written as inverse images of the powers of the kernel ideal sheaves.  For cartesian squares
`i_{U₁} ≫ φ₁ = p₁ ≫ i` and `i_{U₂} ≫ φ₂ = p₂ ≫ i_{U₁}` with étale `φ₁`, `φ₂`, and the outer
rectangle presented through `φ₁₂ = φ₂ ≫ φ₁`, the identification of the outer
rectangle, read through the composition comparison of `p₂ ≫ p₁`, is the inverse image along `p₂`
of the identification of the first square followed by that of the second. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_comp_kernelIdeal (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (sq₁ : IsPullback p₁ iU₁ i φ₁) (hφ₁ : IsEtale B S hS φ₁.hom)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁) (sq₂ : IsPullback p₂ iU₂ iU₁ φ₂)
    (hφ₂ : IsEtale B S hS φ₂.hom) (φ₁₂ : U₂ ⟶ X) (hφ : φ₂ ≫ φ₁ = φ₁₂)
    (sq₁₂ : IsPullback (p₂ ≫ p₁) iU₂ i φ₁₂) (hφ₁₂ : IsEtale B S hS φ₁₂.hom) (n : ℤ) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS (p₂ ≫ p₁) iU₂ i φ₁₂ sq₁₂ hφ₁₂ n).hom =
      (modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules)
          (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom := by
  subst hφ
  have s₁ : (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n).hom
      = (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        ((modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map (kernelIdealSheafZPowEtaleRestrictionIso B S hS
          (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n).hom :=
    congrArg (fun t => (modulePullbackCompIso B S hS p₂ p₁).hom.app
        ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫ t)
      (conormalAlgebraEtaleRestrictionPieceIso_hom_eq_squareCompIso_comp B S hS (p₂ ≫ p₁) iU₂ i
        (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n)
  have s₂ : (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        ((modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂.w.symm).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map (kernelIdealSheafZPowEtaleRestrictionIso B S hS
          (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) sq₁₂ hφ₁₂ n).hom
      = (modulePullback B S hS p₂).map
          (((modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ sq₁.w.symm).app
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
            (modulePullback B S hS iU₁).map
              (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom) ≫
        ((modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ sq₂.w.symm).app
          (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map
          (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom :=
    modulePullbackSquareCompIso_paste_comp B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ sq₁.w.symm
      sq₂.w.symm sq₁₂.w.symm _ _ _ _ _ _
      (kernelIdealSheafZPowEtaleRestrictionIso_comp B S hS i p₁ iU₁ φ₁ sq₁ hφ₁ p₂ iU₂ φ₂ sq₂
        hφ₂ sq₁₂ hφ₁₂ n)
  have s₃ : (modulePullback B S hS p₂).map
          (((modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ sq₁.w.symm).app
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
            (modulePullback B S hS iU₁).map
              (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom) ≫
        ((modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ sq₂.w.symm).app
          (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map
          (kernelIdealSheafZPowEtaleRestrictionIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom
      = (modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules)
          (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom :=
    congrArg₂ (· ≫ ·)
      (congrArg ((modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules))
        (conormalAlgebraEtaleRestrictionPieceIso_hom_eq_squareCompIso_comp B S hS p₁ iU₁ i φ₁ sq₁
          hφ₁ n)).symm
      (conormalAlgebraEtaleRestrictionPieceIso_hom_eq_squareCompIso_comp B S hS p₂ iU₂ iU₁ φ₂ sq₂
        hφ₂ n).symm
  exact s₁.trans (s₂.trans s₃)

/-- **Stacks 09RR is compatible with pasting cartesian squares**: the identification of the
outer rectangle, read through the composition comparison of `p₂ ≫ p₁`, is the inverse image
along `p₂` of the identification of the first square followed by that of the second. This is
`conormalAlgebraEtaleRestrictionPieceIso_comp_kernelIdeal` read through the identification
`(𝒞_{Z/X,*})_n = i^*(𝓘ⁿ)`. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_comp (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (sq₁ : IsPullback p₁ iU₁ i φ₁) (hφ₁ : IsEtale B S hS φ₁.hom)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁) (sq₂ : IsPullback p₂ iU₂ iU₁ φ₂)
    (hφ₂ : IsEtale B S hS φ₂.hom) (φ₁₂ : U₂ ⟶ X) (hφ : φ₂ ≫ φ₁ = φ₁₂)
    (sq₁₂ : IsPullback (p₂ ≫ p₁) iU₂ i φ₁₂) (hφ₁₂ : IsEtale B S hS φ₁₂.hom) (n : ℤ) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS (p₂ ≫ p₁) iU₂ i φ₁₂ sq₁₂ hφ₁₂ n).hom =
      (modulePullback B S hS p₂).map
          (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom := by
  have hA : (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) =
      (modulePullbackCompIso B S hS p₂ p₁).hom.app
        ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) :=
    (app_retype (modulePullbackCompIso B S hS p₂ p₁).hom (conormalAlgebra_piece B S hS i n)).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hm : (modulePullback B S hS p₂).map
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom =
      (modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules)
          (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom :=
    (map_retype (modulePullback B S hS p₂)
      (X₁ := (modulePullback B S hS p₁).obj ((conormalAlgebra B S hS i).piece n))
      (Y₁ := (conormalAlgebra B S hS iU₁).piece n)
      (X₂ := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
      (Y₂ := (modulePullback B S hS iU₁).obj
        (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules) rfl rfl _ _
      ((Category.id_comp _).trans (Category.comp_id _)).symm).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  exact (congrArg (· ≫ _) hA).trans
    ((conormalAlgebraEtaleRestrictionPieceIso_comp_kernelIdeal B S hS i p₁ iU₁ φ₁ sq₁ hφ₁ p₂ iU₂ φ₂
      sq₂ hφ₂
      φ₁₂ hφ sq₁₂ hφ₁₂ n).trans (congrArg (· ≫ _) hm.symm))

/-- **Stacks 09RR is compatible with pasting cartesian squares, after an identification of the
source.**  For an isomorphism `κ : 𝒞 ≅ (𝒞_{Z/X,*})_n`, the pasting law of
`conormalAlgebraEtaleRestrictionPieceIso_comp` with `κ` pulled back first. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_comp_iso (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (sq₁ : IsPullback p₁ iU₁ i φ₁) (hφ₁ : IsEtale B S hS φ₁.hom)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁) (sq₂ : IsPullback p₂ iU₂ iU₁ φ₂)
    (hφ₂ : IsEtale B S hS φ₂.hom) (φ₁₂ : U₂ ⟶ X) (hφ : φ₂ ≫ φ₁ = φ₁₂)
    (sq₁₂ : IsPullback (p₂ ≫ p₁) iU₂ i φ₁₂) (hφ₁₂ : IsEtale B S hS φ₁₂.hom) (n : ℤ)
    {C : Modules.{u, u} B S hS Z.1 Z.2} (κ : C ≅ (conormalAlgebra B S hS i).piece n) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app C ≫
        ((modulePullback B S hS (p₂ ≫ p₁)).mapIso κ ≪≫
          conormalAlgebraEtaleRestrictionPieceIso B S hS (p₂ ≫ p₁) iU₂ i φ₁₂ sq₁₂ hφ₁₂ n).hom =
      (modulePullback B S hS p₂).map
          ((modulePullback B S hS p₁).mapIso κ ≪≫
            conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom := by
  have nat := (modulePullbackCompIso B S hS p₂ p₁).hom.naturality κ.hom
  have main := conormalAlgebraEtaleRestrictionPieceIso_comp B S hS i p₁ iU₁ φ₁ sq₁ hφ₁ p₂
    iU₂ φ₂ sq₂ hφ₂ φ₁₂ hφ sq₁₂ hφ₁₂ n
  refine ((congrArg (_ ≫ ·) (Iso.trans_hom _ _)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) nat.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) main).trans (Category.assoc _ _ _).symm))))).trans ?_
  exact congrArg (· ≫ _) ((congrArg (· ≫ _) (Functor.comp_map _ _ κ.hom)).trans
    (((modulePullback B S hS p₂).map_comp _ _).symm.trans
      (congrArg (modulePullback B S hS p₂).map (Iso.trans_hom ((modulePullback B S hS p₁).mapIso κ)
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n)).symm)))

/-- `conormalAlgebraEtaleRestrictionPieceIso_comp_iso` with the composite upper edge
`p₂ ≫ p₁` presented as a given morphism `p₁₂`, through the transport along `p₂ ≫ p₁ = p₁₂`. -/
theorem conormalAlgebraEtaleRestrictionPieceIso_comp_iso_of_eq (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (sq₁ : IsPullback p₁ iU₁ i φ₁) (hφ₁ : IsEtale B S hS φ₁.hom)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁) (sq₂ : IsPullback p₂ iU₂ iU₁ φ₂)
    (hφ₂ : IsEtale B S hS φ₂.hom) (p₁₂ : Z₂ ⟶ Z) (hp : p₂ ≫ p₁ = p₁₂) (φ₁₂ : U₂ ⟶ X)
    (hφ : φ₂ ≫ φ₁ = φ₁₂) (sq₁₂ : IsPullback p₁₂ iU₂ i φ₁₂) (hφ₁₂ : IsEtale B S hS φ₁₂.hom)
    (n : ℤ) {C : Modules.{u, u} B S hS Z.1 Z.2} (κ : C ≅ (conormalAlgebra B S hS i).piece n) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app C ≫
        eqToHom (congrArg (fun k : Z₂ ⟶ Z => (modulePullback B S hS k).obj C) hp) ≫
        ((modulePullback B S hS p₁₂).mapIso κ ≪≫
          conormalAlgebraEtaleRestrictionPieceIso B S hS p₁₂ iU₂ i φ₁₂ sq₁₂ hφ₁₂ n).hom =
      (modulePullback B S hS p₂).map
          ((modulePullback B S hS p₁).mapIso κ ≪≫
            conormalAlgebraEtaleRestrictionPieceIso B S hS p₁ iU₁ i φ₁ sq₁ hφ₁ n).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS p₂ iU₂ iU₁ φ₂ sq₂ hφ₂ n).hom := by
  subst hp
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
    (conormalAlgebraEtaleRestrictionPieceIso_comp_iso B S hS i p₁ iU₁ φ₁ sq₁ hφ₁ p₂ iU₂ φ₂ sq₂
      hφ₂ φ₁₂ hφ sq₁₂ hφ₁₂ n κ)

end Pasting

section Fibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  {T T' : BigFppfOver B S hS} (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- **The section of the fibre is compatible with the base-change comparison of fibres**: the
section over `x ∘ h` followed by the comparison `𝐏(ℰ)_{T'} ⟶ 𝐏(ℰ)_T` is `h` followed by the
section over `x`. -/
theorem sectionFibreLift_comp_fibreComparison :
    sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h =
      h ≫ sectionFibreLift X E hE hb σ hσ T x := by
  apply Yoneda.fullyFaithful.map_injective
  refine ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T x).hom_ext ?_ ?_
  · have a₁ := RelativeProjPoints.map_fibreComparison_comp_fibreToSpace
      (projectiveBundleSituation X E hE hb).relativeProjPoints T x h
    have a₂ := yoneda_map_sectionFibreLift_comp X E hE hb σ hσ T' (yoneda.map h ≫ x)
    have a₃ := yoneda_map_sectionFibreLift_comp X E hE hb σ hσ T x
    exact ((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) a₁).trans a₂))).trans
      (((congrArg (· ≫ _) (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a₃).trans (Category.assoc _ _ _).symm))).symm)
  · have e₁ : (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h) ≫
          (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x = h :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (RelativeProjPoints.fibreComparison_comp_fibreHom _ T x h)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h)
          (sectionFibreLift_comp_fibreHom X E hE hb σ hσ T' (yoneda.map h ≫ x))).trans
          (Category.id_comp h))))
    have e₂ : (h ≫ sectionFibreLift X E hE hb σ hσ T x) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x = h :=
      (Category.assoc _ _ _).trans ((congrArg (h ≫ ·)
        (sectionFibreLift_comp_fibreHom X E hE hb σ hσ T x)).trans (Category.comp_id h))
    exact ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map e₁)).trans
      ((congrArg yoneda.map e₂).symm.trans (yoneda.map_comp _ _))

/-- The comparison of fibres lies over the comparison of the points of `𝐏(ℰ)`, as morphisms of
algebraic spaces. -/
theorem yonedaSpaceMap_fibreComparison_comp_pointHom :
    yonedaSpaceMap
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h) ≫
        pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x) =
      pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T'
          (yoneda.map h ≫ x)) :=
  ObjectProperty.hom_ext _
    (RelativeProjPoints.map_fibreComparison_comp_fibreToSpace _ T x h)

/-- **The square of sections over a morphism of scheme points is cartesian**: `h`, the two
sections `k_{x ∘ h}`, `k_x`, and the comparison of fibres form a cartesian square of algebraic
spaces, by pasting with the cartesian square of `k_x`. -/
theorem isPullback_sectionFibreLift_fibreComparison :
    IsPullback (yonedaSpaceMap h)
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
      (yonedaSpaceMap
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h)) := by
  have outer : IsPullback (yonedaSpaceMap h ≫ pointHom x)
      (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))) σ
      (yonedaSpaceMap
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h) ≫
        pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x)) :=
    (congrArg (fun g => IsPullback (yonedaSpaceMap h ≫ pointHom x)
        (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))) σ g)
      (yonedaSpaceMap_fibreComparison_comp_pointHom X E hE hb h x)).mpr
      (isPullback_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))
  refine IsPullback.of_right outer ?_
    (isPullback_sectionFibreLift X E hE hb σ hσ T x)
  exact ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    ((congrArg yoneda.map (sectionFibreLift_comp_fibreComparison X E hE hb σ hσ h x)).symm.trans
      (yoneda.map_comp _ _)))

/-- The comparison of fibres along an étale morphism of test objects is étale: it is the base
change of `h` (Stacks 084B). -/
theorem isEtale_fibreComparison (hh : IsEtale B S hS (yoneda.map h)) :
    IsEtale B S hS (yonedaSpaceMap
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h)).hom :=
  isEtale_of_isPullback_yoneda B S hS
    ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback_fibreComparison T x h).flip
    hh

/-- **Naturality of Stacks 09RR at étale scheme points**: along a morphism `h : T' ⟶ T` of test
objects, the identification at the point `x ∘ h` of the conormal module of `σ` with that of the
section `k_{x ∘ h}`, read through the composition comparison of Stacks 03LU and the equality
`h ≫ x = x ∘ h` of points, is the pullback along `h` of the identification at `x` followed by
Stacks 09RR for the cartesian square of sections over `h`
(`isPullback_sectionFibreLift_fibreComparison`). -/
theorem sectionConormalChartIso_naturality (hx : IsEtale B S hS x)
    (hh : IsEtale B S hS (yoneda.map h)) (hx' : IsEtale B S hS (yoneda.map h ≫ x)) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).hom.app
          (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
            (isImmersion_of_isClosedImmersion B S hS
              (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
        eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
            (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
              (isImmersion_of_isClosedImmersion B S hS
                (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
          (rfl : yonedaSpaceMap h ≫ pointHom x = pointHom (yoneda.map h ≫ x))) ≫
        (sectionConormalChartIso X E hE hb σ hσ T' (yoneda.map h ≫ x) hx').hom =
      (modulePullback B S hS (yonedaSpaceMap h)).map
          (sectionConormalChartIso X E hE hb σ hσ T x hx).hom ≫
        (conormalAlgebraEtaleRestrictionPieceIso B S hS (yonedaSpaceMap h)
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
          (yonedaSpaceMap
            ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h))
          (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x)
          (isEtale_fibreComparison X E hE hb h x hh) 1).hom := by
  let κ : (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
      (isImmersion_of_isClosedImmersion B S hS
        (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≅
        (conormalAlgebra B S hS σ).piece 1 :=
    sectionConormalTargetPieceIso X E hE hb σ hσ
  have H := conormalAlgebraEtaleRestrictionPieceIso_comp_iso_of_eq B S hS σ (pointHom x)
    (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x))
    (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x))
    (isPullback_sectionFibreLift X E hE hb σ hσ T x) (isEtale_fibreToSpace X E hE hb T x hx)
    (yonedaSpaceMap h) (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x)))
    (yonedaSpaceMap
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T x h))
    (isPullback_sectionFibreLift_fibreComparison X E hE hb σ hσ h x)
    (isEtale_fibreComparison X E hE hb h x hh) (pointHom (yoneda.map h ≫ x)) rfl
    (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T'
        (yoneda.map h ≫ x)))
    (yonedaSpaceMap_fibreComparison_comp_pointHom X E hE hb h x)
    (isPullback_sectionFibreLift X E hE hb σ hσ T' (yoneda.map h ≫ x))
    (isEtale_fibreToSpace X E hE hb T' (yoneda.map h ≫ x) hx') 1 κ
  have chart : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (hx : IsEtale B S hS x),
      (sectionConormalChartIso X E hE hb σ hσ T x hx).hom =
        ((modulePullback B S hS (pointHom x)).mapIso κ ≪≫
          conormalAlgebraEtaleRestrictionPieceIso B S hS (pointHom x)
            (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T x)) σ
            (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
              ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T x))
            (isPullback_sectionFibreLift X E hE hb σ hσ T x)
            (isEtale_fibreToSpace X E hE hb T x hx) 1).hom :=
    fun _ _ _ => rfl
  rw [chart, chart]
  convert H using 2
  congr 1

end Fibre

end AlgebraicGeometry.Space

end
