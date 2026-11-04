module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparated

/-!
# The stack `𝓜̄_g` is separated, from the quasi-separatedness of `𝓜̄_g` itself

`AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of` proves the statement of Stacks 0E9A
from Stacks 0DSS for the whole stack of curves (`h0DSS`). Its proof, the refined valuative
criterion Stacks 0E95 applied to `𝓜_g → 𝓜̄_g → Spec(ℤ)`, uses of Stacks 0DSS only the local
finite type and the quasi-separatedness of `𝓜̄_g → Spec(ℤ)`. This file runs the same proof from
those two facts directly:

* local finite type of `Curves → Spec(ℤ)` is local finite presentation, which is Stacks 0CMY
  applied to the limit preservation of the stack of curves (`hlim`, Stacks 0D55), through
  `AlgebraicGeometry.isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`;
* the quasi-separatedness of `𝓜̄_g → Spec(ℤ)` (`hqs`) is asked of `𝓜̄_g` only, not of `Curves`.
  By `AlgebraicGeometry.isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact` it follows
  from the quasi-compactness of `Isom_U(Y, X) ⟶ U` for stable families of curves of genus `g`,
  which is the form `isSeparated_moduliStableCurvesOfGenus_of_isQuasiCompact_isom` takes.

## Main results

* `OpenSubstack.isSeparated_inclusion_comp_of_denseTestUniqueness_of_isQuasiSeparated`:
  the refined valuative criterion on an open substack, with the quasi-separatedness asked of the
  open substack only.
* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_isQuasiSeparated`: the statement of
  Stacks 0E9A from `hlim`, `hqs` and the other inputs of
  `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of`.
* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_isQuasiCompact_isom`: the same with
  `hqs` replaced by the quasi-compactness of the isomorphism spaces of stable families of genus
  `g`.

## References

* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.OpenSubstack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The refined valuative criterion of separation on an open substack, quasi-separatedness
asked of the open substack.** Let `f : 𝒳 ⟶ 𝒴` be locally of finite type with `𝒴` locally
Noetherian, let `𝒲 ⊆ 𝒳` be an open substack with `𝒲 ⟶ 𝒴` quasi-separated, and let `T ⊆ |𝒲|` be an
open dense set of points, with open substack `𝒰 ⊆ 𝒲`. If for every valuative square for
`𝒲 ⟶ 𝒴` over a discrete valuation ring whose generic point lies in `𝒰` the category of dotted
arrows is either empty or a setoid with exactly one isomorphism class, then `𝒲 ⟶ 𝒴` is
separated. This is Stacks 0E95 applied to `𝒰 ⟶ 𝒲` and `𝒲 ⟶ 𝒴`. -/
theorem isSeparated_inclusion_comp_of_denseTestUniqueness_of_isQuasiSeparated (f : 𝒳 ⟶ 𝒴)
    (W : OpenSubstack 𝒳)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hWqs : AlgebraicStacks.IsQuasiSeparated B S hS (W.inclusion ≫ f))
    (T : Set (AlgebraicStacks.points B S hS W.toAlgebraicStack))
    (hTo : @IsOpen _ (pointTopology B S hS W.toAlgebraicStack.val) T)
    (hTd : @Dense _ (pointTopology B S hS W.toAlgebraicStack.val) T)
    (hu : ValuativeCriterion.DenseTestUniqueness B S hS (ofIsOpen B S hS T hTo).inclusion
      (W.inclusion ≫ f)) :
    AlgebraicStacks.IsSeparated B S hS (W.inclusion ≫ f) := by
  have hWft : AlgebraicStacks.IsLocallyOfFiniteType B S hS (W.inclusion ≫ f) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ _
      (AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion B S hS W.inclusion
        W.isOpenImmersion) hft
  refine AlgebraicStacks.isSeparated_of_denseTestUniqueness B S hS (W.inclusion ≫ f)
    (ofIsOpen B S hS T hTo).inclusion h𝒴 hWft hWqs
    ((ofIsOpen B S hS T hTo).isFiniteType_inclusion B S hS
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hWft h𝒴)) ?_ hu
  let := pointTopology B S hS W.toAlgebraicStack.val
  exact hTd.mono (pointSet_ofIsOpen T hTo).ge

end AlgebraicGeometry.Stack.OpenSubstack

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The statement of Stacks 0E9A, from the quasi-separatedness of `𝓜̄_g`.** Let `g ≥ 2`, and
let `𝓜̄_g` and `𝓜_g` be the open substacks of the small model of the stack of curves cut out by
being stable of genus `g` (`hP`) and by being smooth with `f_*𝒪_X = 𝒪_S` universally and of genus
`g` (`hQ`). Given the limit preservation of the stack of curves (`hlim`, Stacks 0D55), the
quasi-separatedness of `𝓜̄_g → Spec(ℤ)` (`hqs`), the density of `|𝓜_g|` in `|𝓜̄_g|` (`h0E87`,
Stacks 0E87) and the uniqueness of stable models (`h0E97`, Stacks 0E97), the morphism
`𝓜̄_g → Spec(ℤ)` is separated.

This is the proof of `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of`, with the two
consequences of Stacks 0DSS it uses supplied separately. -/
theorem isSeparated_moduliStableCurvesOfGenus_of_isQuasiSeparated (g : ℕ) (_hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hqs : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (h0E87 : @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ))
    (h0E97 : UniqueStableModels B hZ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) := by
  set W := curvesSmallOpenSubstack B hZ h hP
  set V := curvesSmallOpenSubstack B hZ h hQ
  let T := Stack.AlgebraicStacks.pointsMap B integerBase hZ W.inclusion ⁻¹'
    V.pointSet B integerBase hZ
  have hTo : @IsOpen _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val) T :=
    @IsOpen.preimage _ _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val)
      (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val) _
      (Stack.continuous_pointsMap B integerBase hZ _ _ W.inclusion.hom.hom) _
      (Stack.OpenSubstack.isOpen_pointSet B integerBase hZ V)
  refine Stack.OpenSubstack.isSeparated_inclusion_comp_of_denseTestUniqueness_of_isQuasiSeparated
    B integerBase hZ (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W
    (hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_schemeStack_integerBase.{u, w} B hZ)
    (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim)) hqs T hTo
    h0E87 ?_
  -- the generic object of a square through `𝓜_g` is in `𝓜_g`, and so is everything mapping to it
  have hgen : ∀ (q : Stack.ValuativeSquare B integerBase hZ
      (W.inclusion ≫ Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))),
      (∃ u : Stack.schemeFibredCategory B integerBase hZ
          (siteObject B integerBase hZ q.field_mem
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶
            (Stack.OpenSubstack.ofIsOpen B integerBase hZ T hTo).toAlgebraicStack.1,
        q.x = u ≫ (Stack.OpenSubstack.ofIsOpen B integerBase hZ T hTo).inclusion.hom) →
      ∀ {η : W.toAlgebraicStack.val.val.obj}
        (r : η ⟶ q.x.hom.toFunctor.obj (Over.mk (𝟙 (siteObject B integerBase hZ q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))))),
        IsSmoothH0Family B hZ ((curvesSmallEquivalence B hZ h).inverse.obj η.obj) ∧
          CurveFamily.HasGenus B hZ ((curvesSmallEquivalence B hZ h).inverse.obj η.obj) g := by
    rintro q ⟨u, hu⟩ η r
    have hx : (Stack.OpenSubstack.ofIsOpen B integerBase hZ T hTo).property
        (q.x.hom.toFunctor.obj (Over.mk (𝟙 (siteObject B integerBase hZ q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))))) := by
      rw [hu]
      exact (u.hom.toFunctor.obj _).property
    exact prop_curvesSmallEquivalence_inverse_obj hQ
      (Stack.OpenSubstack.prop_of_hom B integerBase hZ V r.hom
        (Stack.OpenSubstack.property_of_pointsInProperty_preimage B integerBase hZ W V hx))
  -- morphisms of `𝓜̄_g` over a morphism of the site, seen as morphisms of families of curves
  have hlift {U V : BigFppfOver B integerBase hZ} (f : U ⟶ V)
      {a b : W.toAlgebraicStack.val.val.obj} (m : a ⟶ b)
      (hm : W.toAlgebraicStack.val.val.p.IsHomLift f m) :=
    (isHomLift_curvesSmallEquivalence_inverse_map_iff f m.hom).1
      ((Functor.isHomLift_comp_iff W.property.ι _ _ _).1 hm)
  refine Stack.ValuativeSquare.denseTestUniqueness_of_fibre B integerBase hZ _ ?_ ?_
  · intro q hq hu ξ η c r hc hr t ht htc
    have hc' := hlift _ c hc
    have ht' := hlift _ t ht
    have hstab := prop_curvesSmallEquivalence_inverse_obj hP ξ.property
    obtain ⟨hsm, hgenus⟩ := hgen q hu r
    have hηK : (curvesProjectionOver B hZ).obj
        ((curvesSmallEquivalence B hZ h).inverse.obj η.obj) =
        siteObject B integerBase hZ q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) := by
      have := hc'
      exact IsHomLift.domain_eq _ q.genericMap
        ((curvesSmallEquivalence B hZ h).inverse.map c.hom)
    have hξR : (curvesProjectionOver B hZ).obj
        ((curvesSmallEquivalence B hZ h).inverse.obj ξ.obj) =
        siteObject B integerBase hZ q.ring_mem q.base := by
      have := ht'
      exact IsHomLift.domain_eq _ (𝟙 _)
        ((curvesSmallEquivalence B hZ h).inverse.map t.hom)
    obtain ⟨t₀, -, huniq⟩ := h0E97 q.R q.K q.ring_mem q.field_mem q.base q.genericMap
      q.genericMap_left ((curvesSmallEquivalence B hZ h).inverse.map c.hom)
      ((curvesSmallEquivalence B hZ h).inverse.map c.hom) (𝟙 _) hstab hstab hsm hgenus
      hc' hc' (IsHomLift.id hηK)
    have htc' : c.hom ≫ t.hom = c.hom := congrArg (fun m => m.hom) htc
    have h₁ := huniq ((curvesSmallEquivalence B hZ h).inverse.map t.hom)
      ⟨ht', by rw [← Functor.map_comp, htc', Category.id_comp]⟩
    have h₂ := huniq (𝟙 _) ⟨IsHomLift.id hξR, by rw [Category.id_comp, Category.comp_id]⟩
    apply ObjectProperty.hom_ext
    apply (curvesSmallEquivalence B hZ h).inverse.map_injective
    exact h₁.trans (h₂.symm.trans
      ((curvesSmallEquivalence B hZ h).inverse.map_id ξ.obj).symm)
  · intro q hq hu ξ ξ' η η' c c' s r hc hc' hs hr
    have hc₀ := hlift _ c hc
    have hc₀' := hlift _ c' hc'
    have hs₀ := hlift _ s hs
    obtain ⟨hsm, hgenus⟩ := hgen q hu r
    obtain ⟨t₀, ⟨ht₀, htc₀⟩, -⟩ := h0E97 q.R q.K q.ring_mem q.field_mem q.base q.genericMap
      q.genericMap_left ((curvesSmallEquivalence B hZ h).inverse.map c.hom)
      ((curvesSmallEquivalence B hZ h).inverse.map c'.hom)
      ((curvesSmallEquivalence B hZ h).inverse.map s.hom)
      (prop_curvesSmallEquivalence_inverse_obj hP ξ.property)
      (prop_curvesSmallEquivalence_inverse_obj hP ξ'.property) hsm hgenus hc₀ hc₀' hs₀
    let t₁ : ξ.obj ⟶ ξ'.obj := (curvesSmallEquivalence B hZ h).inverse.preimage t₀
    have hmt : (curvesSmallEquivalence B hZ h).inverse.map t₁ = t₀ := Functor.map_preimage _ t₀
    refine ⟨ObjectProperty.homMk t₁, (Functor.isHomLift_comp_iff W.property.ι _ _ _).2
      ((isHomLift_curvesSmallEquivalence_inverse_map_iff _ t₁).2 (by rwa [hmt])), ?_⟩
    apply ObjectProperty.hom_ext
    apply (curvesSmallEquivalence B hZ h).inverse.map_injective
    change (curvesSmallEquivalence B hZ h).inverse.map (c.hom ≫ t₁) =
      (curvesSmallEquivalence B hZ h).inverse.map (s.hom ≫ c'.hom)
    rwa [Functor.map_comp, Functor.map_comp, hmt]

/-- **The statement of Stacks 0E9A, from the quasi-compactness of the isomorphism spaces of
stable curves.** As `isSeparated_moduliStableCurvesOfGenus_of_isQuasiSeparated`, with the
quasi-separatedness of `𝓜̄_g → Spec(ℤ)` supplied by
`AlgebraicGeometry.isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact` from the
quasi-compactness of `Isom_U(Y, X) ⟶ U` for all stable families `Y`, `X` of genus `g` over a common
base (`hqc`). -/
theorem isSeparated_moduliStableCurvesOfGenus_of_isQuasiCompact_isom (g : ℕ) (hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hqc : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base),
      IsStableCurveFamilyOfGenus B hZ g F → IsStableCurveFamilyOfGenus B hZ g G →
      Space.IsQuasiCompact B integerBase hZ
        (CurveFamily.isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))))
    (h0E87 : @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ))
    (h0E97 : UniqueStableModels B hZ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isSeparated_moduliStableCurvesOfGenus_of_isQuasiSeparated B hZ h g hg hP hQ hlim
    (isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact B hZ h hP hqc) h0E87 h0E97

end AlgebraicGeometry

end
