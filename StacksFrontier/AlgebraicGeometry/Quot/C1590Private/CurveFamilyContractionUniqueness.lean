module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionUniquenessScheme
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelNearFibre

/-!
# Uniqueness of contractions of families of curves, étale locally (Stacks 0E89)

Let `X`, `Y₁`, `Y₂` be families of curves and `cᵢ : X ⟶ Yᵢ` morphisms of total spaces over
isomorphisms of bases `bᵢ`. Let `s` be a point of the base of `X`. Suppose that at every
field-valued point over `s` and for all presentations of the fibres by schemes, the morphisms of
fibres `c₁,ₛ` and `c₂,ₛ` are identified by an isomorphism of the targets, the fibre of `X` has
dimension at most one, `𝒪 ≅ c₁,ₛ,*𝒪` and `R¹c₁,ₛ,*𝒪 = 0`. Then there is an étale neighbourhood
`e : U ⟶ S` of `s` over which `Y₁` and `Y₂` are isomorphic compatibly with `c₁` and `c₂`.

This is [Stacks, Tag 0E89] for families of curves, with the open neighbourhood of the statement
replaced by an étale neighbourhood: étale locally on the base the three families are schemes
([Stacks, Tag 0E6F], the hypothesis `h0E6F`), where the scheme case
(`AlgebraicGeometry.C1590Private.exists_openImmersion_iso_of_fibre_of_isPullback`) applies.
Descending the isomorphism to a Zariski neighbourhood is not needed by the consumer
(the stable model of Stacks 0E8A is glued over an étale covering anyway).

## Main definitions

* `AlgebraicGeometry.C1590Private.FibresContractedAlike`: the fibre hypothesis at `s`.
* `AlgebraicGeometry.C1590Private.IsCurveIsoOver`: the conclusion over `e : U ⟶ S`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_open_isCurveIsoOver_of_schemeCharts`: the statement over
  scheme charts.
* `AlgebraicGeometry.C1590Private.exists_etale_iso_of_fibre_contraction`: the statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre hypothesis of Stacks 0E89 at a point `s` of the base of `X`.** At every
field-valued point over `s`, for all presentations of the fibres of `X`, `Y₁`, `Y₂` by schemes and
the induced morphisms of schemes `mᵢ`, the targets of `m₁` and `m₂` are isomorphic over the field
compatibly with `m₁` and `m₂`, the fibre of `X` has dimension at most one, and `m₁` satisfies
`𝒪 ≅ m₁,*𝒪` and `R¹m₁,*𝒪 = 0`. -/
def FibresContractedAlike {X Y₁ Y₂ : CurveFamily B hZ} (b₁ : X.base ⟶ Y₁.base)
    (b₂ : X.base ⟶ Y₂.base) (c₁ : X.total ⟶ Y₁.total) (c₂ : X.total ⟶ Y₂.total)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : Prop :=
  ∀ P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    (∀ x, (BigFppfOver.toScheme B integerBase hZ).map P.value x = s) →
    ∀ ⦃V W₁ W₂ : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject) (w₁ : W₁ ⟶ P.siteObject)
      (w₂ : W₂ ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj) (r₁ : yoneda.obj W₁ ⟶ Y₁.total.obj)
      (r₂ : yoneda.obj W₂ ⟶ Y₂.total.obj) (m₁ : V ⟶ W₁) (m₂ : V ⟶ W₂),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value) →
      IsPullback r₁ (yoneda.map w₁) Y₁.toBase.hom (yonedaEquiv.symm (P.value ≫ b₁)) →
      IsPullback r₂ (yoneda.map w₂) Y₂.toBase.hom (yonedaEquiv.symm (P.value ≫ b₂)) →
      m₁ ≫ w₁ = v → yoneda.map m₁ ≫ r₁ = q ≫ c₁.hom → m₂ ≫ w₂ = v →
      yoneda.map m₂ ≫ r₂ = q ≫ c₂.hom →
        (∃ ε : W₁ ≅ W₂, ε.hom ≫ w₂ = w₁ ∧ m₁ ≫ ε.hom = m₂) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤
          ((1 : ℕ) : WithBot ℕ∞) ∧
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          ((BigFppfOver.toScheme B integerBase hZ).map m₁).toRingCatSheafHom) ∧
        IsZero (((Scheme.Modules.pushforward
          ((BigFppfOver.toScheme B integerBase hZ).map m₁)).rightDerived 1).obj
            (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj V).ringCatSheaf))

/-- **The conclusion of Stacks 0E89 over `e : U ⟶ S`.** For all cartesian presentations `Aᵢ` of
the base changes of `Yᵢ` along `e ≫ bᵢ` and `A` of the base change of `X` along `e`, there is an
isomorphism `A₁ ≅ A₂` over `U` compatible with `c₁` and `c₂`. -/
def IsCurveIsoOver {X Y₁ Y₂ : CurveFamily B hZ} (b₁ : X.base ⟶ Y₁.base) (b₂ : X.base ⟶ Y₂.base)
    (c₁ : X.total ⟶ Y₁.total) (c₂ : X.total ⟶ Y₂.total) {U : BigFppfOver B integerBase hZ}
    (e : U ⟶ X.base) : Prop :=
  ∀ ⦃A₁ A₂ A : AlgebraicSpaces B integerBase hZ⦄ (j₁ : A₁ ⟶ Y₁.total) (p₁ : A₁ ⟶ schemeSpace U)
    (j₂ : A₂ ⟶ Y₂.total) (p₂ : A₂ ⟶ schemeSpace U) (jX : A ⟶ X.total) (pX : A ⟶ schemeSpace U),
    IsPullback j₁ p₁ Y₁.toBase (schemeSpaceMap (e ≫ b₁)) →
    IsPullback j₂ p₂ Y₂.toBase (schemeSpaceMap (e ≫ b₂)) →
    IsPullback jX pX X.toBase (schemeSpaceMap e) →
    ∃ θ : A₁ ≅ A₂, θ.hom ≫ p₂ = p₁ ∧ ∀ (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂),
      a₁ ≫ j₁ = jX ≫ c₁ → a₁ ≫ p₁ = pX → a₂ ≫ j₂ = jX ≫ c₂ → a₂ ≫ p₂ = pX → a₁ ≫ θ.hom = a₂

/-- `yonedaEquiv.symm` of a morphism is its Yoneda image. -/
theorem yonedaEquiv_symm_eq_yoneda_map {C : Type*} [Category C] {A A' : C} (f : A ⟶ A') :
    yonedaEquiv.symm f = yoneda.map f :=
  (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map f).symm

/-- A morphism of schemes between objects of the site over `Spec ℤ` is a morphism of the site. -/
def homOfToScheme {A A' : BigFppfOver B integerBase hZ}
    (f : (BigFppfOver.toScheme B integerBase hZ).obj A ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj A') : A ⟶ A' :=
  Over.homMk ⟨f⟩ (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The morphism of schemes underlying `homOfToScheme f` is `f`. -/
@[simp]
theorem toScheme_map_homOfToScheme {A A' : BigFppfOver B integerBase hZ}
    (f : (BigFppfOver.toScheme B integerBase hZ).obj A ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj A') :
    (BigFppfOver.toScheme B integerBase hZ).map (homOfToScheme f) = f :=
  rfl

/-- Morphisms of the site over `Spec ℤ` are determined by their morphisms of schemes. -/
theorem hom_ext_of_toScheme {A A' : BigFppfOver B integerBase hZ} {f g : A ⟶ A'}
    (h : (BigFppfOver.toScheme B integerBase hZ).map f =
      (BigFppfOver.toScheme B integerBase hZ).map g) : f = g := by
  ext1
  exact ObjectProperty.hom_ext _ h

/-- The residue field of a point of an object of the site, as a field-valued point of a scheme of
the site to which the object maps. -/
def residuePointVia {U Q : BigFppfOver B integerBase hZ} (φ : U ⟶ Q)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj where
  carrier := ((BigFppfOver.toScheme B integerBase hZ).obj U).residueField u
  contained := B.residueField_spec_contains U.left.2 u
  toBase := ((BigFppfOver.toScheme B integerBase hZ).obj U).fromSpecResidueField u ≫ U.hom.1
  value := Space.residueFieldMap B integerBase hZ U u _ ≫ φ

/-- Morphisms of spaces between the spaces of two objects of the site come from the site. -/
private theorem exists_schemeSpaceMap_eq {A A' : BigFppfOver B integerBase hZ}
    (g : schemeSpace A ⟶ schemeSpace A') : ∃ f : A ⟶ A', schemeSpaceMap f = g :=
  ⟨Yoneda.fullyFaithful.preimage g.hom,
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)⟩

/-- Morphisms of the site are determined by their morphisms of spaces. -/
private theorem hom_ext_of_schemeSpaceMap {A A' : BigFppfOver B integerBase hZ} {f g : A ⟶ A'}
    (h : schemeSpaceMap f = schemeSpaceMap g) : f = g :=
  Yoneda.fullyFaithful.map_injective (congrArg (fun k => k.hom) h)

/-- Base change of a chart of a family of curves along a morphism of the site, as a pullback of
spaces. -/
private theorem isPullback_pullback_fst_comp {Y : CurveFamily B hZ}
    {Z U N : BigFppfOver B integerBase hZ} {p : schemeSpace Z ⟶ Y.total} {q : Z ⟶ U}
    {φ : U ⟶ Y.base} (sq : IsPullback p (schemeSpaceMap q) Y.toBase (schemeSpaceMap φ))
    (ν : N ⟶ U) :
    IsPullback (schemeSpaceMap (pullback.fst q ν) ≫ p) (schemeSpaceMap (pullback.snd q ν))
      Y.toBase (schemeSpaceMap (ν ≫ φ)) := by
  rw [schemeSpaceMap_comp]
  exact (isPullback_schemeSpaceMap (IsPullback.of_hasPullback q ν)).paste_horiz sq

/-- **[Stacks, Tag 0E89] over scheme charts.** Let `X`, `Y₁`, `Y₂` be families of curves,
`cᵢ : X ⟶ Yᵢ` over `bᵢ`, and let `φ : U ⟶ X.base` be a morphism of the site over which the three
families are schemes `ZX`, `ZY₁`, `ZY₂`, with `cᵢ` induced by morphisms of schemes `Fᵢ`. If the
fibre hypothesis holds at `s` and `u ∈ U` lies over `s`, there is an open immersion `e` into `U`
with `u` in its image over which `Y₁` and `Y₂` are isomorphic compatibly with `c₁` and `c₂`. -/
theorem exists_open_isCurveIsoOver_of_schemeCharts {X Y₁ Y₂ : CurveFamily B hZ}
    (b₁ : X.base ⟶ Y₁.base) (b₂ : X.base ⟶ Y₂.base) (c₁ : X.total ⟶ Y₁.total)
    (c₂ : X.total ⟶ Y₂.total) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base)
    (hfib : FibresContractedAlike b₁ b₂ c₁ c₂ s)
    {U ZX ZY₁ ZY₂ : BigFppfOver B integerBase hZ} (φ : U ⟶ X.base) (qX : ZX ⟶ U)
    (qY₁ : ZY₁ ⟶ U) (qY₂ : ZY₂ ⟶ U) (pX : schemeSpace ZX ⟶ X.total)
    (pY₁ : schemeSpace ZY₁ ⟶ Y₁.total) (pY₂ : schemeSpace ZY₂ ⟶ Y₂.total) (F₁ : ZX ⟶ ZY₁)
    (F₂ : ZX ⟶ ZY₂) (sqX : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap φ))
    (sqY₁ : IsPullback pY₁ (schemeSpaceMap qY₁) Y₁.toBase (schemeSpaceMap (φ ≫ b₁)))
    (sqY₂ : IsPullback pY₂ (schemeSpaceMap qY₂) Y₂.toBase (schemeSpaceMap (φ ≫ b₂)))
    (hF₁ : F₁ ≫ qY₁ = qX) (hF₁c : schemeSpaceMap F₁ ≫ pY₁ = pX ≫ c₁) (hF₂ : F₂ ≫ qY₂ = qX)
    (hF₂c : schemeSpaceMap F₂ ≫ pY₂ = pX ≫ c₂) (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hu : (BigFppfOver.toScheme B integerBase hZ).map φ u = s) :
    ∃ (U' : BigFppfOver B integerBase hZ) (e : U' ⟶ U),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      u ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      IsCurveIsoOver b₁ b₂ c₁ c₂ (e ≫ φ) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  -- the scheme properties of the charts
  have : IsProper (T.map qX) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqX
  have : Flat (T.map qX) := X.flat_toScheme_map_of_isPullback sqX
  have : LocallyOfFinitePresentation (T.map qX) :=
    X.locallyOfFinitePresentation_toScheme_map_of_isPullback sqX
  have : IsProper (T.map qY₁) := Y₁.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqY₁
  have : Flat (T.map qY₁) := Y₁.flat_toScheme_map_of_isPullback sqY₁
  have : LocallyOfFinitePresentation (T.map qY₁) :=
    Y₁.locallyOfFinitePresentation_toScheme_map_of_isPullback sqY₁
  have : IsProper (T.map qY₂) := Y₂.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqY₂
  have : Flat (T.map qY₂) := Y₂.flat_toScheme_map_of_isPullback sqY₂
  have : LocallyOfFinitePresentation (T.map qY₂) :=
    Y₂.locallyOfFinitePresentation_toScheme_map_of_isPullback sqY₂
  -- the residue field point at `u` and the fibre presentations there
  let P := residuePointVia φ u
  let ν : P.siteObject ⟶ U := Space.residueFieldMap B integerBase hZ U u _
  have hPν : P.value = ν ≫ φ := rfl
  have hPs : ∀ x, T.map P.value x = s := fun x => by
    rw [hPν, Functor.map_comp, Scheme.Hom.comp_apply]
    exact (congrArg (T.map φ) (Scheme.fromSpecResidueField_apply _ _)).trans hu
  have presX := isPullback_pullback_fst_comp sqX ν
  have presY₁ := isPullback_pullback_fst_comp sqY₁ ν
  have presY₂ := isPullback_pullback_fst_comp sqY₂ ν
  set m₁ := pullback.map qX ν qY₁ ν F₁ (𝟙 _) (𝟙 _) (by simp [hF₁]) (by simp)
  set m₂ := pullback.map qX ν qY₂ ν F₂ (𝟙 _) (𝟙 _) (by simp [hF₂]) (by simp)
  have hm₁ : m₁ ≫ pullback.snd qY₁ ν = pullback.snd qX ν :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hm₂ : m₂ ≫ pullback.snd qY₂ ν = pullback.snd qX ν :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hm₁f : m₁ ≫ pullback.fst qY₁ ν = pullback.fst qX ν ≫ F₁ := pullback.lift_fst _ _ _
  have hm₂f : m₂ ≫ pullback.fst qY₂ ν = pullback.fst qX ν ≫ F₂ := pullback.lift_fst _ _ _
  obtain ⟨⟨ε, hε, hεm⟩, hdim, h0, hR⟩ := hfib P hPs (pullback.snd qX ν) (pullback.snd qY₁ ν)
    (pullback.snd qY₂ ν) (schemeSpaceMap (pullback.fst qX ν) ≫ pX).hom
    (schemeSpaceMap (pullback.fst qY₁ ν) ≫ pY₁).hom (schemeSpaceMap (pullback.fst qY₂ ν) ≫ pY₂).hom
    m₁ m₂
    (AlgebraicSpaces.isPullback_hom _ _ _ presX)
    (AlgebraicSpaces.isPullback_hom _ _ _ (by rw [← Category.assoc] at presY₁; exact presY₁))
    (AlgebraicSpaces.isPullback_hom _ _ _ (by rw [← Category.assoc] at presY₂; exact presY₂))
    hm₁ (by
      have e : schemeSpaceMap m₁ ≫ schemeSpaceMap (pullback.fst qY₁ ν) ≫ pY₁ =
          (schemeSpaceMap (pullback.fst qX ν) ≫ pX) ≫ c₁ := by
        rw [← Category.assoc, ← schemeSpaceMap_comp, hm₁f, schemeSpaceMap_comp, Category.assoc,
          hF₁c, Category.assoc]
      exact congrArg (fun k => k.hom) e)
    hm₂ (by
      have e : schemeSpaceMap m₂ ≫ schemeSpaceMap (pullback.fst qY₂ ν) ≫ pY₂ =
          (schemeSpaceMap (pullback.fst qX ν) ≫ pX) ≫ c₂ := by
        rw [← Category.assoc, ← schemeSpaceMap_comp, hm₂f, schemeSpaceMap_comp, Category.assoc,
          hF₂c, Category.assoc]
      exact congrArg (fun k => k.hom) e)
  -- the scheme case over `U`
  obtain ⟨Uo, e, he, ⟨u₀, hu₀⟩, hIso⟩ := exists_openImmersion_iso_of_fibre_of_isPullback
    (K := P.carrier) (T.map ν) u (Scheme.fromSpecResidueField_apply _ _) (T.map qX) (T.map qY₁)
    (T.map qY₂) (T.map F₁) (by rw [← Functor.map_comp, hF₁]) (T.map F₂)
    (by rw [← Functor.map_comp, hF₂]) (T.map (pullback.snd qX ν)) (T.map (pullback.snd qY₁ ν))
    (T.map (pullback.snd qY₂ ν)) (T.map (pullback.fst qX ν)) (T.map (pullback.fst qY₁ ν))
    (T.map (pullback.fst qY₂ ν)) ((IsPullback.of_hasPullback qX ν).map T)
    ((IsPullback.of_hasPullback qY₁ ν).map T) ((IsPullback.of_hasPullback qY₂ ν).map T)
    (T.map m₁) (T.map m₂) (by rw [← Functor.map_comp, hm₁])
    (by rw [← Functor.map_comp, hm₁f, Functor.map_comp]) (by rw [← Functor.map_comp, hm₂])
    (by rw [← Functor.map_comp, hm₂f, Functor.map_comp]) (T.mapIso ε)
    (by rw [Functor.mapIso_hom, ← Functor.map_comp, hε])
    (by rw [Functor.mapIso_hom, ← Functor.map_comp, hεm]) hdim h0 hR
  -- the open of the site
  have hUo : B.Contains Uo := Scheme.size_lt_of_isOpenImmersion e U.left.2
  let U' : BigFppfOver B integerBase hZ := Over.mk (⟨e ≫ U.hom.1⟩ : B.obj hUo ⟶ B.obj hZ)
  let eB : U' ⟶ U := homOfToScheme e
  refine ⟨U', eB, he, ⟨u₀, hu₀⟩, ?_⟩
  intro A₁ A₂ A j₁ p₁ j₂ p₂ jA pA h₁ h₂ hX
  rw [Category.assoc] at h₁ h₂
  -- the charts over `U'`
  have sqU₁ := isPullback_pullback_fst_comp sqY₁ eB
  have sqU₂ := isPullback_pullback_fst_comp sqY₂ eB
  have sqUX := isPullback_pullback_fst_comp sqX eB
  let κ₁ := h₁.isoIsPullback _ _ sqU₁
  let κ₂ := h₂.isoIsPullback _ _ sqU₂
  let κX := hX.isoIsPullback _ _ sqUX
  have hκ₁f : κ₁.hom ≫ schemeSpaceMap (pullback.fst qY₁ eB) ≫ pY₁ = j₁ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hκ₁s : κ₁.hom ≫ schemeSpaceMap (pullback.snd qY₁ eB) = p₁ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hκ₂f : κ₂.hom ≫ schemeSpaceMap (pullback.fst qY₂ eB) ≫ pY₂ = j₂ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hκ₂s : κ₂.hom ≫ schemeSpaceMap (pullback.snd qY₂ eB) = p₂ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hκXf : κX.inv ≫ jA = schemeSpaceMap (pullback.fst qX eB) ≫ pX :=
    IsPullback.isoIsPullback_inv_fst _ _ _ _
  have hκXs : κX.inv ≫ pA = schemeSpaceMap (pullback.snd qX eB) :=
    IsPullback.isoIsPullback_inv_snd _ _ _ _
  -- the scheme isomorphism, as an isomorphism of the site
  obtain ⟨θs, hθs, hθc⟩ := hIso (T.map (pullback.fst qY₁ eB)) (T.map (pullback.snd qY₁ eB))
    (T.map (pullback.fst qY₂ eB)) (T.map (pullback.snd qY₂ eB)) (T.map (pullback.fst qX eB))
    (T.map (pullback.snd qX eB)) ((IsPullback.of_hasPullback qY₁ eB).map T)
    ((IsPullback.of_hasPullback qY₂ eB).map T) ((IsPullback.of_hasPullback qX eB).map T)
  let θB : pullback qY₁ eB ≅ pullback qY₂ eB :=
    { hom := homOfToScheme θs.hom
      inv := homOfToScheme θs.inv
      hom_inv_id := hom_ext_of_toScheme (by
        rw [Functor.map_comp, toScheme_map_homOfToScheme, toScheme_map_homOfToScheme,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id])
      inv_hom_id := hom_ext_of_toScheme (by
        rw [Functor.map_comp, toScheme_map_homOfToScheme, toScheme_map_homOfToScheme,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id]) }
  have hθBs : θB.hom ≫ pullback.snd qY₂ eB = pullback.snd qY₁ eB :=
    hom_ext_of_toScheme (by rw [Functor.map_comp]; exact hθs)
  refine ⟨κ₁ ≪≫ (schemeSpaceFunctor B integerBase hZ).mapIso θB ≪≫ κ₂.symm, ?_, ?_⟩
  · change κ₁.hom ≫ schemeSpaceMap θB.hom ≫ κ₂.inv ≫ p₂ = p₁
    rw [← hκ₂s, Iso.inv_hom_id_assoc, ← schemeSpaceMap_comp, hθBs, hκ₁s]
  · intro a₁ a₂ ha₁ hp₁ ha₂ hp₂
    -- the morphisms of charts induced by `a₁` and `a₂`
    have hlift : ∀ {ZY : BigFppfOver B integerBase hZ} {qY : ZY ⟶ U} {Yi : CurveFamily B hZ}
        {bi : X.base ⟶ Yi.base} {pY : schemeSpace ZY ⟶ Yi.total}
        {Ai : AlgebraicSpaces B integerBase hZ}
        {ji : Ai ⟶ Yi.total} {pi : Ai ⟶ schemeSpace U'} {ci : X.total ⟶ Yi.total}
        {F : ZX ⟶ ZY}
        (_ : IsPullback pY (schemeSpaceMap qY) Yi.toBase (schemeSpaceMap (φ ≫ bi)))
        (_ : F ≫ qY = qX) (_ : schemeSpaceMap F ≫ pY = pX ≫ ci)
        (κ : Ai ≅ schemeSpace (pullback qY eB))
        (_ : κ.hom ≫ schemeSpaceMap (pullback.fst qY eB) ≫ pY = ji)
        (_ : κ.hom ≫ schemeSpaceMap (pullback.snd qY eB) = pi) (ai : A ⟶ Ai),
        ai ≫ ji = jA ≫ ci → ai ≫ pi = pA →
          ∃ α : pullback qX eB ⟶ pullback qY eB, schemeSpaceMap α = κX.inv ≫ ai ≫ κ.hom ∧
            α ≫ pullback.fst qY eB = pullback.fst qX eB ≫ F := by
      intro ZY qY Yi bi pY Ai ji pi ci F sqY hF hFc κ hκf hκs ai hai hpi
      obtain ⟨α, hα⟩ := exists_schemeSpaceMap_eq (κX.inv ≫ ai ≫ κ.hom)
      refine ⟨α, hα, ?_⟩
      have h : schemeSpaceMap (α ≫ pullback.fst qY eB) =
          schemeSpaceMap (pullback.fst qX eB ≫ F) := by
        apply sqY.hom_ext
        · rw [schemeSpaceMap_comp, schemeSpaceMap_comp, Category.assoc, Category.assoc, hFc, hα,
            Category.assoc, Category.assoc, hκf, hai, ← Category.assoc, hκXf, Category.assoc]
        · rw [schemeSpaceMap_comp, schemeSpaceMap_comp, Category.assoc, Category.assoc,
            ← schemeSpaceMap_comp, ← schemeSpaceMap_comp F, hF, pullback.condition,
            schemeSpaceMap_comp, ← Category.assoc, hα]
          simp only [Category.assoc]
          rw [reassoc_of% hκs, reassoc_of% hpi, ← Category.assoc, hκXs, ← schemeSpaceMap_comp,
            ← schemeSpaceMap_comp, pullback.condition]
      exact hom_ext_of_schemeSpaceMap h
    obtain ⟨α₁, hα₁, hα₁f⟩ := hlift sqY₁ hF₁ hF₁c κ₁ hκ₁f hκ₁s a₁ ha₁ hp₁
    obtain ⟨α₂, hα₂, hα₂f⟩ := hlift sqY₂ hF₂ hF₂c κ₂ hκ₂f hκ₂s a₂ ha₂ hp₂
    have hc := hθc (T.map α₁) (T.map α₂) (by rw [← Functor.map_comp, hα₁f, Functor.map_comp])
      (by rw [← Functor.map_comp, hα₂f, Functor.map_comp])
    have hαθ : α₁ ≫ θB.hom = α₂ := hom_ext_of_toScheme (by rw [Functor.map_comp]; exact hc)
    have := congrArg schemeSpaceMap hαθ
    rw [schemeSpaceMap_comp, hα₁, hα₂] at this
    change a₁ ≫ κ₁.hom ≫ schemeSpaceMap θB.hom ≫ κ₂.inv = a₂
    rw [← cancel_epi κX.inv, ← cancel_mono κ₂.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact this

/-- **[Stacks, Tag 0E89] for families of curves, étale locally.** Let `X`, `Y₁`, `Y₂` be families
of curves and `cᵢ : X ⟶ Yᵢ` morphisms of total spaces over isomorphisms of bases `bᵢ`, and let `s`
be a point of the base of `X`. Suppose that at every field-valued point over `s`, for all
presentations of the fibres by schemes, the morphisms of fibres `c₁,ₛ` and `c₂,ₛ` are identified by
an isomorphism of their targets, the fibre of `X` has dimension at most one, `𝒪 ≅ c₁,ₛ,*𝒪` and
`R¹c₁,ₛ,*𝒪 = 0` (`AlgebraicGeometry.C1590Private.FibresContractedAlike`). Then there is an étale
`e : U ⟶ X.base` with `s` in its image over which `Y₁` and `Y₂` are isomorphic compatibly with `c₁`
and `c₂` (`AlgebraicGeometry.C1590Private.IsCurveIsoOver`).

The source concludes over an open neighbourhood of `s`; here the neighbourhood is étale, because
the families are schemes only étale locally ([Stacks, Tag 0E6F], the hypothesis `h0E6F`, not yet
proved here). Over the scheme charts the statement is
`AlgebraicGeometry.C1590Private.exists_open_isCurveIsoOver_of_schemeCharts`. -/
theorem exists_etale_iso_of_fibre_contraction (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    {X Y₁ Y₂ : CurveFamily B hZ} (b₁ : X.base ⟶ Y₁.base) (b₂ : X.base ⟶ Y₂.base) [IsIso b₁]
    [IsIso b₂] (c₁ : X.total ⟶ Y₁.total) (c₂ : X.total ⟶ Y₂.total)
    (hc₁ : c₁ ≫ Y₁.toBase = X.toBase ≫ schemeSpaceMap b₁)
    (hc₂ : c₂ ≫ Y₂.toBase = X.toBase ≫ schemeSpaceMap b₂)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base)
    (hfib : FibresContractedAlike b₁ b₂ c₁ c₂ s) :
    ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ X.base),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map e) ∧
      IsCurveIsoOver b₁ b₂ c₁ c₂ e := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  -- charts for `X` and `Y₁`, and for `Y₂`
  obtain ⟨U₁, ZX, ZY₁, φ₁, qX, qY₁, pX, pY₁, f₁, hφ₁, ⟨u₁, hu₁⟩, -, sqX, sqY₁, hf₁, hf₁c⟩ :=
    exists_schemeCharts h0E6F b₁ c₁ hc₁ (T.map b₁ s)
  obtain ⟨U₃, Z₃, φ₃, q₃, p₃, hφ₃, ⟨u₃, hu₃⟩, sq₃⟩ := h0E6F Y₂ (T.map b₂ s)
  set φ := φ₁ ≫ inv b₁
  have hφb₁ : φ ≫ b₁ = φ₁ := by simp [φ]
  have sqY₁b : IsPullback pY₁ (schemeSpaceMap qY₁) Y₁.toBase (schemeSpaceMap (φ ≫ b₁)) :=
    hφb₁ ▸ sqY₁
  have : Etale (T.map φ₁) := hφ₁
  have : Etale (T.map φ₃) := hφ₃
  have : Etale (T.map φ) := by
    rw [Functor.map_comp]
    infer_instance
  -- the common chart `U = U₁ ×_{Y₂.base} U₃`
  obtain ⟨β, hβ⟩ : ∃ β : U₁ ⟶ Y₂.base, β = φ ≫ b₂ := ⟨_, rfl⟩
  have : Etale (T.map β) := by
    rw [hβ, Functor.map_comp]
    infer_instance
  let π₁ := pullback.fst β φ₃
  let π₃ := pullback.snd β φ₃
  have hπ : π₁ ≫ β = π₃ ≫ φ₃ := pullback.condition
  have hUT := (IsPullback.of_hasPullback β φ₃).map T
  have : Etale (T.map π₁) := MorphismProperty.of_isPullback hUT.flip inferInstance
  have hu : T.map φ u₁ = s := by
    change T.map (inv b₁) (T.map φ₁ u₁) = s
    rw [hu₁, ← Scheme.Hom.comp_apply, ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hu₁₃ : T.map β u₁ = T.map φ₃ u₃ := by
    rw [hu₃, hβ, Functor.map_comp, Scheme.Hom.comp_apply, hu]
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback u₁ u₃ hu₁₃
  let u := hUT.isoPullback.inv z
  have huπ : T.map π₁ u = u₁ := by
    rw [← hz₁, ← hUT.isoPullback_inv_fst, Scheme.Hom.comp_apply]
  -- the three charts over `U`
  have sqX' := isPullback_pullback_fst_comp sqX π₁
  have sqY₁' := isPullback_pullback_fst_comp sqY₁b π₁
  have sqY₂' := isPullback_pullback_fst_comp sq₃ π₃
  rw [← Category.assoc] at sqY₁'
  have sqY₂'' : IsPullback (schemeSpaceMap (pullback.fst q₃ π₃) ≫ p₃)
      (schemeSpaceMap (pullback.snd q₃ π₃)) Y₂.toBase (schemeSpaceMap ((π₁ ≫ φ) ≫ b₂)) := by
    rw [Category.assoc, ← hβ, hπ]
    exact sqY₂'
  have sqX'' : IsPullback (schemeSpaceMap (pullback.fst qX π₁) ≫ pX)
      (schemeSpaceMap (pullback.snd qX π₁)) X.toBase (schemeSpaceMap (π₁ ≫ φ)) := sqX'
  -- the morphisms of charts
  let F₁ := pullback.map qX π₁ qY₁ π₁ f₁ (𝟙 _) (𝟙 _) (by simp [hf₁]) (by simp)
  have hF₁ : F₁ ≫ pullback.snd qY₁ π₁ = pullback.snd qX π₁ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hF₁c : schemeSpaceMap F₁ ≫ schemeSpaceMap (pullback.fst qY₁ π₁) ≫ pY₁ =
      (schemeSpaceMap (pullback.fst qX π₁) ≫ pX) ≫ c₁ := by
    rw [← Category.assoc, ← schemeSpaceMap_comp, pullback.lift_fst, schemeSpaceMap_comp,
      Category.assoc, hf₁c, Category.assoc]
  let g₂ : schemeSpace (pullback qX π₁) ⟶ schemeSpace (pullback q₃ π₃) :=
    sqY₂''.lift ((schemeSpaceMap (pullback.fst qX π₁) ≫ pX) ≫ c₂)
      (schemeSpaceMap (pullback.snd qX π₁)) (by
        rw [Category.assoc, hc₂, ← Category.assoc, sqX''.w, Category.assoc,
          ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, Category.assoc])
  obtain ⟨F₂, hF₂g⟩ := exists_schemeSpaceMap_eq g₂
  have hF₂ : F₂ ≫ pullback.snd q₃ π₃ = pullback.snd qX π₁ := by
    apply hom_ext_of_schemeSpaceMap
    rw [schemeSpaceMap_comp, hF₂g]
    exact sqY₂''.lift_snd _ _ _
  have hF₂c : schemeSpaceMap F₂ ≫ schemeSpaceMap (pullback.fst q₃ π₃) ≫ p₃ =
      (schemeSpaceMap (pullback.fst qX π₁) ≫ pX) ≫ c₂ := by
    rw [hF₂g]
    exact sqY₂''.lift_fst _ _ _
  -- the chart case
  obtain ⟨U', eB, heB, ⟨u', hu'⟩, hiso⟩ := exists_open_isCurveIsoOver_of_schemeCharts b₁ b₂ c₁ c₂ s
    hfib (π₁ ≫ φ) (pullback.snd qX π₁) (pullback.snd qY₁ π₁) (pullback.snd q₃ π₃)
    (schemeSpaceMap (pullback.fst qX π₁) ≫ pX) (schemeSpaceMap (pullback.fst qY₁ π₁) ≫ pY₁)
    (schemeSpaceMap (pullback.fst q₃ π₃) ≫ p₃) F₁ F₂ sqX'' sqY₁' sqY₂'' hF₁ hF₁c hF₂ hF₂c u
    (by rw [Functor.map_comp, Scheme.Hom.comp_apply, huπ, hu])
  refine ⟨U', eB ≫ π₁ ≫ φ, ?_, ⟨u', ?_⟩, hiso⟩
  · have := heB
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hu', huπ,
      hu]

end AlgebraicGeometry.C1590Private

end
