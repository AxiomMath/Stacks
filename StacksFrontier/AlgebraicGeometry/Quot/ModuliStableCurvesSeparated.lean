module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves
public import StacksFrontier.AlgebraicGeometry.Stacks.DottedArrowSchemeTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackDenseTestSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackPropertyBridges
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# The stack `𝓜̄_g` is separated (towards Stacks 0E9A)

Let `g ≥ 2`. Stacks 0E9A says that `𝓜̄_g → Spec(ℤ)` is separated. Its proof applies the refined
Noetherian valuative criterion (Stacks 0E95) to `𝓜_g → 𝓜̄_g` and `𝓜̄_g → Spec(ℤ)`:

* `𝓜̄_g → Spec(ℤ)` is quasi-separated and locally of finite presentation because `𝓜̄_g` is an
  open substack of `Curves` (Stacks 0DSS); so `𝓜̄_g` is locally Noetherian (Stacks 06R6);
* `𝓜_g → 𝓜̄_g` is an open immersion with dense image (Stacks 0E87), and quasi-compact (Stacks
  0CPM), hence of finite type;
* unwinding the categories of dotted arrows of a valuative square over a discrete valuation ring
  `R` with generic point in `𝓜_g`, what has to be shown is the uniqueness of stable models
  (Stacks 0E97).

This file carries out that proof on the small model `curvesAlgebraicStack B hZ h` of the stack of
curves. The unwinding is done in two steps: the hypothesis of Stacks 0E95 for a 1-morphism into
`Spec(ℤ)` is read in the fibres of the source by the 2-Yoneda lemma
(`AlgebraicGeometry.Stack.ValuativeSquare.denseTestUniqueness_of_fibre`), and the fibres of the
small model are read as families of curves through the equivalence
`AlgebraicGeometry.curvesSmallEquivalence`. In the fibres, an object of `𝓜̄_g` over `Spec R` is a
stable family of curves of genus `g` over `R`, an arrow into it over `Spec K ⟶ Spec R` identifies
its generic fibre, and an arrow over `𝟙` is an isomorphism of families; Stacks 0E97 is exactly the
statement that an isomorphism of the generic fibres, which are smooth, extends uniquely.

## Main results

* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of`: the statement of Stacks 0E9A, from
  explicit inputs.

## Implementation notes

The result is stated with explicit inputs and carries no `stacks` attribute. The inputs are the
statements of other tags: the algebraicity of the stack of curves (`h`, Stacks 0D5A), the openness
of the loci `𝓜̄_g` and `𝓜_g` (`hP`, Stacks 0E78; `hQ`, Stacks 0E83), Stacks 0DSS (`h0DSS`, on the
small model), the density of `|𝓜_g|` in `|𝓜̄_g|` (`h0E87`, Stacks 0E87, read on the points of the
algebraic stack `𝓜̄_g`) and the uniqueness of stable models (`h0E97`, Stacks 0E97, read for
families of curves over the spectrum of a discrete valuation ring). Stacks 0E95, Stacks 06R6 and
Stacks 0CPM are used as proved results.

## References

* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The uniqueness of stable models, read for families of curves** (the statement of Stacks
0E97 used in the proof of Stacks 0E9A). Let `R` be a discrete valuation ring with fraction field
`K`, `gm : Spec K ⟶ Spec R` the canonical map. Let `F`, `F'` be stable families of curves of genus
`g` over `Spec R`, with generic fibres `c : G ⟶ F` and `c' : G' ⟶ F'` (morphisms of families of
curves over `gm`), and let `s : G ⟶ G'` be an isomorphism of the generic fibres over `Spec K`,
where `G` is smooth with `H⁰ = K` universally and of genus `g`. Then there is a unique isomorphism
`t : F ⟶ F'` over `Spec R` restricting to `s`. -/
def UniqueStableModels (g : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ integerBase)
    (gm : siteObject B integerBase hZ hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B integerBase hZ hR base),
    (B.inclusion).map gm.left = Spec.map (CommRingCat.ofHom (algebraMap R K)) →
    ∀ {F F' G G' : CurveFamily B hZ} (c : G ⟶ F) (c' : G' ⟶ F') (s : G ⟶ G'),
      IsStableCurveFamilyOfGenus B hZ g F → IsStableCurveFamilyOfGenus B hZ g F' →
      IsSmoothH0Family B hZ G → CurveFamily.HasGenus B hZ G g →
      (curvesProjectionOver B hZ).IsHomLift gm c → (curvesProjectionOver B hZ).IsHomLift gm c' →
      (curvesProjectionOver B hZ).IsHomLift
        (𝟙 (siteObject B integerBase hZ hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base))) s →
      ∃! t : F ⟶ F', (curvesProjectionOver B hZ).IsHomLift
        (𝟙 (siteObject B integerBase hZ hR base)) t ∧ c ≫ t = s ≫ c'

variable {B hZ h} in
/-- A morphism of the small model of the stack of curves lies over a morphism of the site exactly
when its image family of curves does. -/
theorem isHomLift_curvesSmallEquivalence_inverse_map_iff {U V : BigFppfOver B integerBase hZ}
    (f : U ⟶ V) {ξ η : (curvesAlgebraicStack B hZ h).val.val.obj} (φ : ξ ⟶ η) :
    (curvesAlgebraicStack B hZ h).val.val.p.IsHomLift f φ ↔
      (curvesProjectionOver B hZ).IsHomLift f ((curvesSmallEquivalence B hZ h).inverse.map φ) :=
  ⟨fun hφ => by
    have hφ' : (curvesSmallBased B hZ).p.IsHomLift f φ := hφ
    exact Functor.isHomLift_map_of_comp_eq (curvesSmallEquivalenceOver B hZ).inv.w f φ,
    fun hφ => Functor.isHomLift_of_isHomLift_map_of_comp_eq
      (curvesSmallEquivalenceOver B hZ).inv.w f φ hφ⟩

variable {B hZ h} in
/-- An object of the small model lying in an open substack `Curves^P` is the image of a family of
curves with `P`, up to the counit of the equivalence. -/
theorem prop_curvesSmallEquivalence_inverse_obj {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) {ξ : (curvesAlgebraicStack B hZ h).val.val.obj}
    (hξ : (curvesSmallOpenSubstack B hZ h hP).property ξ) :
    P ((curvesSmallEquivalence B hZ h).inverse.obj ξ) :=
  (curvesSmallOpenSubstack_property_iff B hZ h hP _).1
    (Stack.OpenSubstack.prop_of_hom B integerBase hZ _
      ((curvesSmallEquivalence B hZ h).counitIso.hom.app ξ) hξ)

/-- The stack `Spec(ℤ)` over the site has a locally Noetherian scheme atlas. -/
theorem hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_schemeStack_integerBase :
    Stack.HasPropertyOnSomeSchemeAtlas B integerBase hZ
      (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))) := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj
      (Over.mk (𝟙 (B.obj hZ)))) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (ULift.{u} ℤ))))
  exact Stack.isLocallyNoetherianStack_schemeStack B integerBase hZ _

/-- **The statement of Stacks 0E9A, from explicit inputs.** Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g`
be the open substacks of the small model of the stack of curves cut out by being stable of genus
`g` (`hP`) and by being smooth with `f_*𝒪_X = 𝒪_S` universally and of genus `g` (`hQ`). Given
Stacks 0DSS (`h0DSS`), the density of `|𝓜_g|` in `|𝓜̄_g|` (`h0E87`, Stacks 0E87) and the
uniqueness of stable models (`h0E97`, Stacks 0E97), the morphism `𝓜̄_g → Spec(ℤ)` is separated.

This is the source's proof: Stacks 0E95 applied to `𝓜_g → 𝓜̄_g → Spec(ℤ)`, with the categories
of dotted arrows unwound into stable models. -/
theorem isSeparated_moduliStableCurvesOfGenus_of (g : ℕ) (_hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (h0DSS : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
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
  refine Stack.OpenSubstack.isSeparated_inclusion_comp_of_denseTestUniqueness B integerBase hZ
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W
    (hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_schemeStack_integerBase.{u, w} B hZ)
    (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      h0DSS.2) h0DSS.1 T hTo h0E87 ?_
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
  set E := (curvesSmallEquivalence B hZ h).inverse
  have hlift : ∀ {U U' : BigFppfOver B integerBase hZ} {f : U ⟶ U'}
      {ξ η : W.property.FullSubcategory} (c : ξ ⟶ η), W.toAlgebraicStack.1.1.p.IsHomLift f c →
      (curvesProjectionOver B hZ).IsHomLift f (E.map c.hom) :=
    fun c hc => (isHomLift_curvesSmallEquivalence_inverse_map_iff _ c.hom).1
      ((Functor.isHomLift_comp_iff W.property.ι _ _ _).1 hc)
  refine Stack.ValuativeSquare.denseTestUniqueness_of_fibre B integerBase hZ _ ?_ ?_
  · intro q hq hu ξ η c r hc hr t ht htc
    have := hq
    have hc' := hlift c hc
    have ht' := hlift t ht
    have hstab := prop_curvesSmallEquivalence_inverse_obj hP ξ.property
    obtain ⟨hsm, hgenus⟩ := hgen q hu r
    have hηK : (curvesProjectionOver B hZ).obj
        (E.obj η.obj) =
        siteObject B integerBase hZ q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) := by
      have := hc'
      exact IsHomLift.domain_eq _ q.genericMap
        (E.map c.hom)
    have hξR : (curvesProjectionOver B hZ).obj
        (E.obj ξ.obj) =
        siteObject B integerBase hZ q.ring_mem q.base := by
      have := ht'
      exact IsHomLift.domain_eq _ (𝟙 _)
        (E.map t.hom)
    obtain ⟨t₀, -, huniq⟩ := h0E97 q.R q.K q.ring_mem q.field_mem q.base q.genericMap
      q.genericMap_left (E.map c.hom)
      (E.map c.hom) (𝟙 _) hstab hstab hsm hgenus
      hc' hc' (IsHomLift.id hηK)
    have htc' : c.hom ≫ t.hom = c.hom := congrArg (fun m => m.hom) htc
    have h₁ := huniq (E.map t.hom)
      ⟨ht', by rw [← Functor.map_comp, htc', Category.id_comp]⟩
    have h₂ := huniq (𝟙 _) ⟨IsHomLift.id hξR, by rw [Category.id_comp, Category.comp_id]⟩
    apply ObjectProperty.hom_ext
    apply E.map_injective
    change E.map t.hom =
      E.map (𝟙 ξ.obj)
    exact h₁.trans (h₂.symm.trans
      (E.map_id ξ.obj).symm)
  · intro q hq hu ξ ξ' η η' c c' s r hc hc' hs hr
    have := hq
    have hc₀ := hlift c hc
    have hc₀' := hlift c' hc'
    have hs₀ := hlift s hs
    obtain ⟨hsm, hgenus⟩ := hgen q hu r
    obtain ⟨t₀, ⟨ht₀, htc₀⟩, -⟩ := h0E97 q.R q.K q.ring_mem q.field_mem q.base q.genericMap
      q.genericMap_left (E.map c.hom)
      (E.map c'.hom)
      (E.map s.hom)
      (prop_curvesSmallEquivalence_inverse_obj hP ξ.property)
      (prop_curvesSmallEquivalence_inverse_obj hP ξ'.property) hsm hgenus hc₀ hc₀' hs₀
    let t₁ : ξ.obj ⟶ ξ'.obj := E.preimage t₀
    have hmt : E.map t₁ = t₀ :=
      Functor.map_preimage _ t₀
    refine ⟨ObjectProperty.homMk t₁, ?_, ?_⟩
    · refine (Functor.isHomLift_comp_iff W.property.ι _ _ _).2 ?_
      refine (isHomLift_curvesSmallEquivalence_inverse_map_iff _ t₁).2 ?_
      rwa [hmt]
    · apply ObjectProperty.hom_ext
      apply E.map_injective
      change E.map (c.hom ≫ t₁) =
        E.map (s.hom ≫ c'.hom)
      rwa [Functor.map_comp, Functor.map_comp, hmt]

end AlgebraicGeometry

end
