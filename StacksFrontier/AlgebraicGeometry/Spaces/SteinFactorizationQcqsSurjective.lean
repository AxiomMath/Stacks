module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral

/-!
# The morphism to the normalization is surjective, over an affine base

Let `f : X ⟶ Y` be a universally closed and quasi-separated morphism of algebraic spaces over a
scheme `S`, and let `X ⟶ Y' ⟶ Y` be the normalization of `Y` in `X` (Stacks 0822).  Stacks 0A19,
clause (1), asserts among other things that `f' : X ⟶ Y'` is surjective.  This file proves it
when `Y` is represented by an affine scheme `T`; then `Y'` is represented by an affine scheme
`T'`, integral over `T`.

The source argues with the closed image of `f'` and a function `h` on `Y'` vanishing on it.  The
proof here reaches the same two facts — `f'` is universally closed, and the functions on `Y'`
inject into the functions on `X` — the second one through the universal property of the
normalization (Stacks 0823), which is the form in which the library knows `Y'`:

* let `k : Γ(T', 𝒪) ⟶ Γ(X, 𝒪_X)` be pullback along `X ⟶ Y' ≅ T'` and `J` its kernel.  The
  morphism `X ⟶ T'` factors through the closed subscheme `Z = Spec(Γ(T', 𝒪)/J)`, which is
  integral over `T`, so the universal property yields `Y' ⟶ Z` over `Y` under `X`.  Followed by
  `Z ⟶ T' ≅ Y'` it is the identity of `Y'`, again by the universal property, so the closed
  immersion `Z ⟶ T'` has a section and `J = 0`;
* an affine surjective étale chart `P` of the quasi-compact space `X` then has dense image in
  `T'`, because `Γ(T', 𝒪) ⟶ Γ(X, 𝒪_X) ⟶ Γ(P, 𝒪_P)` is injective, and `X ⟶ T'` is universally
  closed (Stacks 04NX, `T' ⟶ T` being separated), so its image is closed and dense.

## Main results

* `AlgebraicGeometry.Space.exists_specFactorization_of_globalHom`: a morphism `W ⟶ V` from an
  algebraic space to an affine object of the site factors through `Spec C` for every finite
  type `Γ(V, 𝒪)`-algebra `C` through which pullback of functions factors.
* `AlgebraicGeometry.Space.injective_pullbackToGlobalFunctions_of_isRelativeNormalization`:
  the functions on a represented affine normalization inject into the functions on the source.
* `AlgebraicGeometry.Space.isSurjective_of_isRelativeNormalization_of_isAffine`: the
  morphism to a represented affine normalization is surjective when `f` is universally closed.
* `AlgebraicGeometry.Space.isSurjective_toNormalizationInQcqs_of_isAffine`: the case of the
  normalization of Stacks 0822 over an affine base.

## References

* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring through the spectrum of a finite type algebra -/

/-- **A morphism to an affine object of the site factors through `Spec C`.**  Let `W` be an
algebraic space over `S`, `V` an object of the site with affine underlying scheme and
`p : W ⟶ V`.  Let `ρ : Γ(V, 𝒪) →+* C` be of finite type and `κ : C →+* Γ(W, 𝒪_W)` such that
`κ ∘ ρ` is pullback of functions along `p` on every étale scheme chart of `W`.  Then `Spec C`
is the scheme of an object `Z` of the site over `V`, compatibly with `Spec ρ`, and `p` factors
through `Z`. -/
theorem exists_specFactorization_of_globalHom
    {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : W.obj ⟶ yoneda.obj V) (C : Type u) [CommRing C]
    (ρ : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* C) (hρ : RingHom.FiniteType ρ)
    (κ : C →+* globalFunctions B S hS W.obj)
    (hcompat : ∀ c : SmallEtale B S hS W.obj,
      (globalFunctionsChartRestriction B S hS W c).comp (κ.comp ρ) =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c)).appTop.hom) :
    ∃ (Z : BigFppfOver B S hS) (z : Z ⟶ V)
      (e : Spec (CommRingCat.of C) ≅ (BigFppfOver.toScheme B S hS).obj Z)
      (π : W.obj ⟶ yoneda.obj Z),
      e.hom ≫ (BigFppfOver.toScheme B S hS).map z =
          Spec.map (CommRingCat.ofHom ρ) ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ∧
        π ≫ yoneda.map z = p := by
  have := hV
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ρ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hρ
  set zv : Spec (CommRingCat.of C) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    Spec.map (CommRingCat.ofHom ρ) ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
    with hzvdef
  have : LocallyOfFiniteType zv := by rw [hzvdef]; infer_instance
  have : QuasiCompact zv := by rw [hzvdef]; infer_instance
  obtain ⟨Z, z, e, he⟩ := exists_siteObject_of_locallyOfFiniteType B S hS zv
  obtain ⟨π₀, hπ₀⟩ := exists_specMap_of_globalHom B S hS W C κ
  set c₀ := chosenAtlasPairTarget B S hS W
  set χ := (globalFunctionsChartRestriction B S hS W c₀).comp κ with hχdef
  have hchart : specMapOfGlobalHom C χ ≫ zv =
      (BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c₀) := by
    rw [hzvdef]
    refine specMapOfGlobalHom_comp_specMap_comp_isoSpec_inv ρ χ _ ?_
    rw [← hcompat c₀, hχdef]
    rfl
  have hEq : π₀ ≫ schemePointsMap B S hS zv = p ≫ yonedaToSchemePoints B S hS V := by
    refine hom_ext_of_etale_atlas B S hS W.property.isSheaf
      (isSheaf_schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj V)) c₀.obj.hom
      (surjective_chosenAtlasPairTarget B S hS W) c₀.property ?_
    refine yonedaEquiv.injective ?_
    have hL : yonedaEquiv (c₀.obj.hom ≫ π₀ ≫ schemePointsMap B S hS zv) =
        specMapOfGlobalHom C χ ≫ zv := by
      rw [← Category.assoc, yonedaEquiv_comp_schemePointsMap]
      exact congrArg (fun k => k ≫ zv) (hπ₀ c₀)
    have hR : yonedaEquiv (c₀.obj.hom ≫ p ≫ yonedaToSchemePoints B S hS V) =
        (BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c₀) := by
      rw [← Category.assoc, ← yoneda_map_smallEtaleChartMapToBase B S hS p c₀, yonedaEquiv_comp,
        yonedaEquiv_yoneda_map]
      exact yonedaToSchemePoints_app B S hS V _ _
    exact hL.trans (hchart.trans hR.symm)
  have hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj.obj U),
      (π₀ ≫ schemePointsMap B S hS e.hom).app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (p.app U w) := by
    intro U w
    have h1 : (π₀ ≫ schemePointsMap B S hS e.hom).app U w = π₀.app U w ≫ e.hom := rfl
    rw [h1, Category.assoc, he]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hEq U) w
  exact ⟨Z, z, e, liftToYoneda B S hS (π₀ ≫ schemePointsMap B S hS e.hom) z p hq, he,
    liftToYoneda_comp_yoneda_map B S hS (π₀ ≫ schemePointsMap B S hS e.hom) z p hq⟩

/-! ### Functions on a represented affine normalization -/

section RelativeNormalization

variable {B S hS} {X : AlgebraicSpaces B S hS} {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {F : X.obj ⟶ Y} {ν : Y' ⟶ Y} {f' : X.obj ⟶ Y'} {T T' : BigFppfOver B S hS}

/-- Transporting the normalization map `f'` along `inv e` and then `p` recovers `F`. -/
private theorem comp_inv_comp_yoneda_map_comp_eq (eY : yoneda.obj T ⟶ Y) (e : yoneda.obj T' ⟶ Y')
    [IsIso e] (p : T' ⟶ T) (hrel : IsRelativeNormalization B S hS F ν f')
    (hsq : yoneda.map p ≫ eY = e ≫ ν) : (f' ≫ inv e) ≫ yoneda.map p ≫ eY = F := by
  rw [Category.assoc, hsq, IsIso.inv_hom_id_assoc, hrel.fac]

/-- **The functions on a represented affine normalization inject into the functions on the
source.**  Let `f' : X ⟶ Y'` and `ν : Y' ⟶ Y` exhibit `Y'` as the normalization of `Y` in `X`,
and let `Y` and `Y'` be represented by objects `T` and `T'` of the site, `T'` affine, compatibly
with an integral morphism of schemes `p : T' ⟶ T`.  Then pullback of functions along
`X ⟶ Y' ≅ T'` is injective.

With `J` the kernel, `X ⟶ T'` factors through the closed subscheme `Spec(Γ(T', 𝒪)/J)`, which is
integral over `T`; the universal property of the normalization gives a morphism `Y' ⟶ Spec(…)`
which, followed by the closed immersion, is the identity of `Y' ≅ T'`, so the quotient map has
a left inverse. -/
theorem injective_pullbackToGlobalFunctions_of_isRelativeNormalization
    (eY : yoneda.obj T ⟶ Y) [IsIso eY] (e : yoneda.obj T' ⟶ Y') [IsIso e] (p : T' ⟶ T)
    (hrel : IsRelativeNormalization B S hS F ν f')
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hp : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p))
    (hsq : yoneda.map p ≫ eY = e ≫ ν) :
    Function.Injective (pullbackToGlobalFunctions B S hS X T'
      (ObjectProperty.homMk (f' ≫ (inv e : Y' ⟶ yoneda.obj T')) : X ⟶ schemeSpace T')) := by
  classical
  have := hT'
  set f₀ : X.obj ⟶ yoneda.obj T' := f' ≫ inv e with hf₀
  set k := pullbackToGlobalFunctions B S hS X T'
    (ObjectProperty.homMk (f' ≫ (inv e : Y' ⟶ yoneda.obj T')) : X ⟶ schemeSpace T')
  set J := RingHom.ker k
  set ρ : Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) →+*
      (Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) ⧸ J) := Ideal.Quotient.mk J
  have hρsurj : Function.Surjective ρ := Ideal.Quotient.mk_surjective
  have hρft : RingHom.FiniteType ρ := RingHom.FiniteType.of_surjective ρ hρsurj
  have hκρ : (RingHom.kerLift k).comp ρ = k := RingHom.ext fun r => RingHom.kerLift_mk k r
  have hcompat : ∀ c : SmallEtale B S hS X.obj,
      (globalFunctionsChartRestriction B S hS X c).comp ((RingHom.kerLift k).comp ρ) =
        ((BigFppfOver.toScheme B S hS).map
          (smallEtaleChartMapToBase B S hS f₀ c)).appTop.hom := by
    intro c
    rw [hκρ]
    exact RingHom.ext fun s =>
      pullbackToGlobalFunctions_apply_chart B S hS X T'
        (ObjectProperty.homMk (f' ≫ (inv e : Y' ⟶ yoneda.obj T')) : X ⟶ schemeSpace T') c s
  obtain ⟨Z, z, eZ, π, heZ, hπ⟩ := exists_specFactorization_of_globalHom B S hS hT' f₀ _ ρ hρft
    (RingHom.kerLift k) hcompat
  -- `Z ⟶ T` is integral
  have hzmap : (BigFppfOver.toScheme B S hS).map z = eZ.inv ≫
      Spec.map (CommRingCat.ofHom ρ) ≫ ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv := by
    rw [← heZ, Iso.inv_hom_id_assoc]
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ)) :=
    IsClosedImmersion.spec_of_surjective _ hρsurj
  have := hp
  have hzp :
      _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map (z ≫ p)) := by
    rw [Functor.map_comp, hzmap]
    infer_instance
  have hπZ : IsIntegralHom B S hS (yoneda.map (z ≫ p) ≫ eY) :=
    isIntegralHom_comp B S hS (isIntegralHom_yoneda_map B S hS _ hzp)
      (isIntegralHom_of_isIso B S hS eY)
  have hf₀F : f₀ ≫ yoneda.map p ≫ eY = F :=
    comp_inv_comp_yoneda_map_comp_eq eY e p hrel hsq
  have hπF : π ≫ yoneda.map (z ≫ p) ≫ eY = F := by
    rw [Functor.map_comp, ← Category.assoc π, ← Category.assoc, hπ, Category.assoc, hf₀F]
  obtain ⟨h, ⟨hh, hhν⟩, -⟩ :=
    hrel.existsUnique_lift (isAlgebraicSpace_yoneda B S hS Z) _ hπZ π hπF
  have hT'int : IsIntegralHom B S hS (yoneda.map p ≫ eY) :=
    isIntegralHom_comp B S hS (isIntegralHom_yoneda_map B S hS _ hp)
      (isIntegralHom_of_isIso B S hS eY)
  obtain ⟨_, -, huniq⟩ :=
    hrel.existsUnique_lift (isAlgebraicSpace_yoneda B S hS T') _ hT'int f₀ hf₀F
  have hsplit : h ≫ yoneda.map z = inv e := by
    refine (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨rfl, by rw [hsq, IsIso.inv_hom_id_assoc]⟩).symm
    · rw [← Category.assoc, hh, hπ]
    · rw [Category.assoc, ← Category.assoc (yoneda.map z), ← Functor.map_comp, hhν]
  -- the closed immersion `Z ⟶ T'` has a section
  set s₀ : T' ⟶ Z := yoneda.preimage (e ≫ h)
  have hs₀ : s₀ ≫ z = 𝟙 T' := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, hsplit, IsIso.hom_inv_id,
      yoneda.map_id]
  have hs₀' : (BigFppfOver.toScheme B S hS).map s₀ ≫ (BigFppfOver.toScheme B S hS).map z =
      𝟙 _ := by
    rw [← Functor.map_comp, hs₀, (BigFppfOver.toScheme B S hS).map_id]
  set r : Spec Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) ⟶ Spec (CommRingCat.of
      (Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) ⧸ J)) :=
    ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv ≫
      (BigFppfOver.toScheme B S hS).map s₀ ≫ eZ.inv
  have h3 : (BigFppfOver.toScheme B S hS).map s₀ ≫ eZ.inv ≫ Spec.map (CommRingCat.ofHom ρ) =
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom := by
    have h2 : ((BigFppfOver.toScheme B S hS).map s₀ ≫ eZ.inv ≫ Spec.map (CommRingCat.ofHom ρ)) ≫
        ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv = 𝟙 _ := by
      simpa only [Category.assoc, hzmap] using hs₀'
    rw [Iso.comp_inv_eq, Category.id_comp] at h2
    exact h2
  have hr : r ≫ Spec.map (CommRingCat.ofHom ρ) = 𝟙 _ := by
    simp only [r, Category.assoc, h3, Iso.inv_hom_id]
  set σ := Spec.preimage r
  have hσ : CommRingCat.ofHom ρ ≫ σ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hr, Spec.map_id]
    rfl
  intro a b hab
  have hρab : ρ a = ρ b := by
    change Ideal.Quotient.mk J a = Ideal.Quotient.mk J b
    rw [Ideal.Quotient.eq]
    exact (RingHom.mem_ker).2 (by rw [map_sub, hab, sub_self])
  have := congrArg σ.hom hρab
  have hid : ∀ x, σ.hom (ρ x) = x := fun x =>
    ConcreteCategory.congr_hom hσ x
  rwa [hid, hid] at this

/-- **The morphism to a represented affine normalization is surjective.**  Let `f' : X ⟶ Y'` and
`ν : Y' ⟶ Y` exhibit `Y'` as the normalization of `Y` in `X` along a universally closed
`F : X ⟶ Y`, and let `Y` and `Y'` be represented by affine objects `T` and `T'` of the site,
compatibly with an integral morphism of schemes `p : T' ⟶ T`.  Then `f'` is surjective.

`X ⟶ T'` is universally closed, `T' ⟶ T` being separated (Stacks 04NX), so its image is closed;
an affine surjective étale chart of the quasi-compact space `X` has dense image in `T'`, because
the functions on `T'` inject into the functions on `X`
(`AlgebraicGeometry.Space.injective_pullbackToGlobalFunctions_of_isRelativeNormalization`)
and these into the functions on the chart. -/
theorem isSurjective_of_isRelativeNormalization_of_isAffine (hY : IsAlgebraicSpace B S hS Y)
    (eY : yoneda.obj T ⟶ Y) [IsIso eY] (e : yoneda.obj T' ⟶ Y') [IsIso e] (p : T' ⟶ T)
    (hrel : IsRelativeNormalization B S hS F ν f') (huc : UniversallyClosed B S hS F)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hp : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p))
    (hsq : yoneda.map p ≫ eY = e ≫ ν) :
    IsSurjective B S hS f' := by
  have := hT
  have := hT'
  set f₀ : X.obj ⟶ yoneda.obj T' := f' ≫ inv e with hf₀
  have hf₀p : f₀ ≫ yoneda.map p = F ≫ inv eY := by
    rw [IsIso.eq_comp_inv, Category.assoc, comp_inv_comp_yoneda_map_comp_eq eY e p hrel hsq]
  have huc' : UniversallyClosed B S hS (F ≫ inv eY) :=
    universallyClosed_comp B S hS hY (isAlgebraicSpace_yoneda B S hS T) F (inv eY) huc
      (universallyClosed_of_isIso B S hS (inv eY))
  have := hp
  have hsep : IsSeparated B S hS (yoneda.map p) :=
    (isSeparated_yoneda_map_iff B S hS p).2 (AlgebraicGeometry.IsSeparated.of_isAffineHom _)
  have hf₀uc : UniversallyClosed B S hS f₀ :=
    universallyClosed_of_comp_of_isSeparated B S hS X.property
      (isAlgebraicSpace_yoneda B S hS T') (isAlgebraicSpace_yoneda B S hS T) f₀ (yoneda.map p)
      (by rw [hf₀p]; exact huc') hsep
  -- an affine surjective étale chart of `X`
  have hXqc : IsQuasiCompactSpace B S hS X.obj :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS T hT X.property
      (isAlgebraicSpace_yoneda B S hS T) (F ≫ inv eY) huc'
  obtain ⟨c₀, hc₀aff, hc₀surj⟩ :
      ∃ c : SmallEtale B S hS X.obj,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.obj).obj c)) ∧
          (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
            (BigFppfOver.toScheme B S hS)).presheaf c.obj.hom := by
    obtain ⟨P, a, hPaff, haSurj, haEtale⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.obj
        X.property).1 hXqc
    exact ⟨chartFromEtaleHom B S hS X P a (presheaf_etale_of_isEtale B S hS haEtale), hPaff,
      haSurj⟩
  have := hc₀aff
  set g₀ := smallEtaleChartMapToBase B S hS f₀ c₀
  -- the chart has dense image in `T'`
  have happ : ((BigFppfOver.toScheme B S hS).map g₀).appTop.hom =
      (globalFunctionsChartRestriction B S hS X c₀).comp
        (pullbackToGlobalFunctions B S hS X T'
          (ObjectProperty.homMk (f' ≫ (inv e : Y' ⟶ yoneda.obj T')) : X ⟶ schemeSpace T')) :=
    RingHom.ext fun s => (pullbackToGlobalFunctions_apply_chart B S hS X T'
      (ObjectProperty.homMk (f' ≫ (inv e : Y' ⟶ yoneda.obj T')) : X ⟶ schemeSpace T') c₀ s).symm
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map g₀).appTop.hom := by
    rw [happ]
    exact (injective_globalFunctionsChartRestriction_of_isSurjective B S hS X c₀
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.obj X.property _
        c₀.obj.hom).1 hc₀surj)).comp
      (injective_pullbackToGlobalFunctions_of_isRelativeNormalization eY e p hrel hT' hp hsq)
  have hdense : DenseRange ((BigFppfOver.toScheme B S hS).map g₀).base := by
    have key : ∀ {P Q : Scheme.{u}} [IsAffine P] [IsAffine Q] (m : P ⟶ Q),
        Function.Injective m.appTop.hom → DenseRange m.base := by
      intro P Q _ _ m hm
      have h1 : specMapOfGlobalHom Γ(Q, ⊤) m.appTop.hom = m ≫ Q.isoSpec.hom := by
        rw [specMapOfGlobalHom, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]
        rfl
      have hd := denseRange_base_specMapOfGlobalHom m.appTop.hom hm
      rw [h1] at hd
      have hd2 : DenseRange (Q.isoSpec.inv.base ∘ (m ≫ Q.isoSpec.hom).base) :=
        (Scheme.Hom.surjective Q.isoSpec.inv).denseRange.comp hd
          Q.isoSpec.inv.base.hom.continuous
      have hfun : (Q.isoSpec.inv.base ∘ (m ≫ Q.isoSpec.hom).base) = m.base := by
        funext x
        change (m ≫ Q.isoSpec.hom ≫ Q.isoSpec.inv).base x = m.base x
        rw [Iso.hom_inv_id, Category.comp_id]
      rw [hfun] at hd2
      exact hd2
    exact key _ hinj
  have hf₀surj : IsSurjective B S hS f₀ :=
    isSurjective_of_universallyClosed_of_denseRange B S hS f₀ hf₀uc c₀.obj.hom g₀
      (yoneda_map_smallEtaleChartMapToBase B S hS f₀ c₀) hdense
  have hf' : f₀ ≫ e = f' := by rw [hf₀, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hf']
  exact isSurjective_comp B S hS hf₀surj (isSurjective_of_isIso B S hS e)

end RelativeNormalization

/-! ### The normalization of Stacks 0822 over an affine base -/

/-- **The morphism to the normalization is surjective over an affine base.**  Let `f : X ⟶ Y`
be universally closed, quasi-compact and quasi-separated, with `Y` represented by an affine
object `T` of the site, and let `X ⟶ Y' ⟶ Y` be the normalization of `Y` in `X`
(Stacks 0822).  Then `f' : X ⟶ Y'` is surjective. -/
theorem isSurjective_toNormalizationInQcqs_of_isAffine {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (huc : UniversallyClosed B S hS f.hom) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (eY : yoneda.obj T ⟶ Y.obj)
    [IsIso eY] :
    IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom := by
  obtain ⟨T', p, e, hpb, hT', hp⟩ := isIntegralHom_normalizationInQcqsHom f hfqc hfqs T hT eY
  have : IsIso e := hpb.isIso_fst_of_isIso
  exact isSurjective_of_isRelativeNormalization_of_isAffine Y.property eY e p
    (isRelativeNormalization_normalizationInQcqs f hfqc hfqs) huc hT hT' hp hpb.w.symm

end AlgebraicGeometry.Space

end
