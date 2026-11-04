module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorValuationRing
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSiteSpecDictionary

/-!
# Two points of the relative Picard functor over a valuation ring which agree generically

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`, the standing data of Stacks 0D25, and
let `R` be a valuation ring with fraction field `K` whose spectrum is a test scheme over `B`. Let
`x, y` be two elements of `Pic_{X/B}(Spec R)` with the same restriction to `Spec K`. After an
extension of valuation rings `R ⟶ R'`, with fraction field `K'`, both become the classes of
invertible modules `L, N` on `X_{R'}`, and `L` and `N` have the same Picard class on the generic
fibre `X_{K'}`.

This is the reduction, in the proof of Stacks 0DNJ, of the uniqueness part of the valuative
criterion for `Pic_{X/B} ⟶ B` to a statement about invertible modules on `X_{R'}`: the source
replaces `R` by an extension so that `a` comes from an invertible module, and then reads
`a|_{Spec K} = 0` as the triviality of that module on the generic fibre.

## Main results

* `AlgebraicGeometry.Space.specSiteObjectHom`: the morphism of site objects over `S` of a ring
  homomorphism, for any structure morphism of the target equal to the induced one.
* `AlgebraicGeometry.Space.PicardSituation.exists_valuationRing_extension_picardMap_generic_eq`:
  the statement above.

## Implementation notes

The extension is built in three steps. First the intersection of the image sieves of `x` and `y`
for the sheafification map covers, so after one extension `R ⟶ R₁` both are classes of invertible
modules `L₁, N₁`. Their restrictions to the fraction field `K₁` of `R₁` have the same image in the
Picard functor, so by the equalizer sieve they agree after an extension `K₁ ⟶ R₃`, which is a
valuation ring containing `K₁` but in general not a field. Finally the composite
`R₁ ⟶ K₁ ⟶ R₃ ⟶ Frac(R₃)` factors locally through a valuation subring `R'` of `Frac(R₃)`
(Stacks 00IA, `IsLocalRing.exists_factor_valuationRing`), whose fraction field is `Frac(R₃)`; over
it `L₁` and `N₁` agree on the generic fibre because they do after `R₃`.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of site objects over `S` induced by a ring homomorphism `θ : R →+* C`, for any
structure morphism `a'` of `Spec C` equal to the one induced from `a` through `θ`. -/
def specSiteObjectHom {R C : Type u} [CommRing R] [CommRing C] (θ : R →+* C)
    (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) (a' : Spec (.of C) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom θ) ≫ a = a') :
    siteObject B S hS hC a' ⟶ siteObject B S hS hR a :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom θ))) (by
    subst ha
    rfl)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.specSiteObjectHom`. -/
@[simp]
theorem inclusion_map_specSiteObjectHom_left {R C : Type u} [CommRing R] [CommRing C]
    (θ : R →+* C) (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) (a' : Spec (.of C) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom θ) ≫ a = a') :
    B.inclusion.map (specSiteObjectHom (hS := hS) θ hR hC a a' ha).left =
      Spec.map (CommRingCat.ofHom θ) :=
  rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.specSiteObjectMap`. -/
@[simp]
theorem inclusion_map_specSiteObjectMap_left {R C : Type u} [CommRing R] [CommRing C]
    (θ : R →+* C) (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) :
    B.inclusion.map (specSiteObjectMap (hS := hS) θ hR hC a).left =
      Spec.map (CommRingCat.ofHom θ) :=
  rfl

/-- The morphism of test schemes over an algebraic space `Z` induced by a ring homomorphism
`θ : R →+* C`, for site objects over `S` and structure morphisms to `Z` compatible with it. -/
def testSchemeHom {Z : AlgebraicSpaces B S hS} {R C : Type u} [CommRing R] [CommRing C]
    (θ : R →+* C) (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) (a' : Spec (.of C) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom θ) ≫ a = a')
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hR a) ⟶ Z)
    (h' : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hC a') ⟶ Z)
    (hh : (schemeSpaceFunctor B S hS).map (specSiteObjectHom θ hR hC a a' ha) ≫ h = h') :
    (CostructuredArrow.mk h' : SchemesOver Z) ⟶ CostructuredArrow.mk h :=
  CostructuredArrow.homMk (specSiteObjectHom θ hR hC a a' ha) hh

/-- Two morphisms of test schemes agree when their underlying morphisms of schemes do. -/
theorem testScheme_hom_ext {Z : AlgebraicSpaces B S hS} {T T' : SchemesOver Z} {p q : T' ⟶ T}
    (h : B.inclusion.map p.left.left = B.inclusion.map q.left.left) : p = q :=
  CostructuredArrow.hom_ext _ _ (siteObject_hom_ext h)

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- **Two points of `Pic_{X/B}(Spec R)` which agree over the fraction field are, after an
extension of valuation rings, the classes of two invertible modules which agree on the generic
fibre.** Let `R` be a valuation ring with fraction field `K`, `Spec R ⟶ B` a test scheme, and
`x, y` elements of the Picard functor at it whose restrictions to `Spec K` agree. Then there are a
valuation ring `R'` with fraction field `K'`, a local homomorphism `φ : R →+* R'` and a
compatible `ψ : K →+* K'`, and two Picard classes `L, N` of `X_{Spec R'}` with images the
restrictions of `x` and `y`, whose pullbacks to `X_{Spec K'}` agree. -/
theorem exists_valuationRing_extension_picardMap_generic_eq
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R))) (field_mem : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base) ⟶ s.base)
    (x y : s.picardFunctor.obj (Opposite.op (CostructuredArrow.mk h)))
    (hxy : s.picardFunctor.map
        (valuationRingExtensionHom (algebraMap R K) ring_mem field_mem base h).op x =
      s.picardFunctor.map
        (valuationRingExtensionHom (algebraMap R K) ring_mem field_mem base h).op y) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (K' : Type u) (_ : Field K') (_ : Algebra R' K') (_ : IsFractionRing R' K')
      (ring_mem' : B.Contains (Spec (.of R'))) (field_mem' : B.Contains (Spec (.of K')))
      (φ : R →+* R') (ψ : K →+* K'),
      IsLocalHom φ ∧ (algebraMap R' K').comp φ = ψ.comp (algebraMap R K) ∧
      ∃ L N : s.picardAt (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
          (specSiteObjectMap φ ring_mem ring_mem' base) ≫ h)),
        s.picardClassMap _ L =
          s.picardFunctor.map (valuationRingExtensionHom φ ring_mem ring_mem' base h).op x ∧
        s.picardClassMap _ N =
          s.picardFunctor.map (valuationRingExtensionHom φ ring_mem ring_mem' base h).op y ∧
        s.picardMap (valuationRingExtensionHom (algebraMap R' K') ring_mem' field_mem'
            (Spec.map (CommRingCat.ofHom φ) ≫ base) _) L =
          s.picardMap (valuationRingExtensionHom (algebraMap R' K') ring_mem' field_mem'
            (Spec.map (CommRingCat.ofHom φ) ≫ base) _) N := by
  classical
  obtain ⟨R₁, _, _, _, φ₁, hφ₁, ring_mem₁, hmem⟩ :=
    exists_valuationRing_extension_mem_of_mem_restrictedTopology R ring_mem base h
      (s.fppfTopology.intersection_covering
        (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor x)
        (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor y))
  obtain ⟨⟨L₁, hL₁⟩, ⟨N₁, hN₁⟩⟩ := hmem
  have : IsLocalHom φ₁ := hφ₁.2
  let g₁ := valuationRingExtensionHom φ₁ ring_mem ring_mem₁ base h
  let h₁ := (schemeSpaceFunctor B S hS).map (specSiteObjectMap φ₁ ring_mem ring_mem₁ base) ≫ h
  let base₁ := Spec.map (CommRingCat.ofHom φ₁) ≫ base
  let K₁ := FractionRing R₁
  have field_mem₁ : B.Contains (Spec (.of K₁)) := contains_spec_fractionRing ring_mem₁
  have hinj₁ : Function.Injective ((algebraMap R₁ K₁).comp φ₁) :=
    (IsFractionRing.injective R₁ K₁).comp hφ₁.1
  let ψ₁ : K →+* K₁ := IsFractionRing.lift (A := R) (K := K) hinj₁
  have hψ₁ : ψ₁.comp (algebraMap R K) = (algebraMap R₁ K₁).comp φ₁ := by
    ext r
    exact IsFractionRing.lift_algebraMap (A := R) (K := K) hinj₁ r
  let gK₁ := valuationRingExtensionHom (algebraMap R₁ K₁) ring_mem₁ field_mem₁ base₁ h₁
  let gK := valuationRingExtensionHom (algebraMap R K) ring_mem field_mem base h
  have hbaseK₁ : Spec.map (CommRingCat.ofHom ψ₁) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)) ≫ base₁ := by
    simp only [base₁, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ₁]
  let m : (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (specSiteObjectMap
      (algebraMap R₁ K₁) ring_mem₁ field_mem₁ base₁) ≫ h₁) : s.SchemesOver) ⟶
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
        (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫ h) :=
    testSchemeHom ψ₁ field_mem field_mem₁ _ _ hbaseK₁ _ _ (by
      simp only [h₁, ← Functor.map_comp_assoc]
      congr 2
      exact siteObject_hom_ext (by
        simp only [Functor.map_comp, Over.comp_left, inclusion_map_specSiteObjectHom_left,
          inclusion_map_specSiteObjectMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ₁]))
  have hmK : m ≫ gK = gK₁ ≫ g₁ := testScheme_hom_ext (by
    simp only [CostructuredArrow.comp_left, Over.comp_left, Functor.map_comp, m, gK, gK₁, g₁,
      testSchemeHom, CostructuredArrow.homMk_left, valuationRingExtensionHom,
      inclusion_map_specSiteObjectHom_left, inclusion_map_specSiteObjectMap_left,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ₁])
  have key : ∀ {U : s.SchemesOver} (g : U ⟶ CostructuredArrow.mk h₁) M z,
      s.picardClassMap _ M = s.picardFunctor.map g₁.op z →
      s.picardClassMap _ (s.picardMap g M) = s.picardFunctor.map (g ≫ g₁).op z := fun g M z hM => by
    rw [s.picardClassMap_picardMap g M, hM, ← Functor.map_comp_apply, ← op_comp]
  have hK₁ : s.picardClassMap _ (s.picardMap gK₁ L₁) = s.picardClassMap _ (s.picardMap gK₁ N₁) := by
    rw [key gK₁ L₁ x hL₁, key gK₁ N₁ y hN₁, ← hmK, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply, hxy]
  obtain ⟨R₃, _, _, _, ι, hι, ring_mem₃, h₃⟩ :=
    exists_valuationRing_extension_picardMap_eq s K₁ field_mem₁
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)) ≫ base₁)
      ((schemeSpaceFunctor B S hS).map (specSiteObjectMap (algebraMap R₁ K₁) ring_mem₁
        field_mem₁ base₁) ≫ h₁) (s.picardMap gK₁ L₁) (s.picardMap gK₁ N₁) hK₁
  let K₃ := FractionRing R₃
  have field_mem₃ : B.Contains (Spec (.of K₃)) := contains_spec_fractionRing ring_mem₃
  let f₀ : R₁ →+* K₃ := (algebraMap R₃ K₃).comp (ι.comp (algebraMap R₁ K₁))
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f₀
  let φ₄ : R₁ →+* A := f₀.codRestrict A.toSubring hA
  have : IsLocalHom φ₄ := hloc
  have ring_mem₄ : B.Contains (Spec (.of A)) :=
    BigFppfSite.contains_spec_of_injective B field_mem₃ (algebraMap A K₃)
      (IsFractionRing.injective A K₃)
  have hφ₄ : (algebraMap A K₃).comp φ₄ = f₀ := rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, K₃, inferInstance, inferInstance,
    inferInstance, ring_mem₄, field_mem₃, φ₄.comp φ₁, ((algebraMap R₃ K₃).comp ι).comp ψ₁,
    inferInstance, ?_, ?_⟩
  · ext r
    exact congrArg ((algebraMap R₃ K₃).comp ι) (RingHom.congr_fun hψ₁ r).symm
  have hbase₄ : Spec.map (CommRingCat.ofHom φ₄) ≫ base₁ =
      Spec.map (CommRingCat.ofHom (φ₄.comp φ₁)) ≫ base := by
    simp only [base₁, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let g₄ : (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (φ₄.comp φ₁) ring_mem ring_mem₄ base) ≫ h) : s.SchemesOver) ⟶
      CostructuredArrow.mk h₁ :=
    testSchemeHom φ₄ ring_mem₁ ring_mem₄ base₁ _ hbase₄ _ _ (by
      simp only [h₁, ← Functor.map_comp_assoc]
      congr 2
      exact siteObject_hom_ext (by
        simp only [Functor.map_comp, Over.comp_left, inclusion_map_specSiteObjectHom_left,
          inclusion_map_specSiteObjectMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]))
  have hg₄ : g₄ ≫ g₁ = valuationRingExtensionHom (φ₄.comp φ₁) ring_mem ring_mem₄ base h :=
    testScheme_hom_ext (by
      simp only [CostructuredArrow.comp_left, Over.comp_left, Functor.map_comp, g₄, g₁,
        testSchemeHom, CostructuredArrow.homMk_left, valuationRingExtensionHom,
        inclusion_map_specSiteObjectHom_left, inclusion_map_specSiteObjectMap_left,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  refine ⟨s.picardMap g₄ L₁, s.picardMap g₄ N₁, ?_, ?_, ?_⟩
  · rw [key g₄ L₁ x hL₁, hg₄]
  · rw [key g₄ N₁ y hN₁, hg₄]
  · let g₃ := valuationRingExtensionHom ι field_mem₁ ring_mem₃
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)) ≫ base₁)
      ((schemeSpaceFunctor B S hS).map (specSiteObjectMap (algebraMap R₁ K₁) ring_mem₁
        field_mem₁ base₁) ≫ h₁)
    have hbase' : Spec.map (CommRingCat.ofHom (algebraMap R₃ K₃)) ≫
        Spec.map (CommRingCat.ofHom ι) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R₁ K₁)) ≫ base₁ =
        Spec.map (CommRingCat.ofHom (algebraMap A K₃)) ≫
          Spec.map (CommRingCat.ofHom (φ₄.comp φ₁)) ≫ base := by
      simp only [base₁, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    let m' := testSchemeHom (Z := s.base) (algebraMap R₃ K₃) ring_mem₃ field_mem₃ _ _ hbase'
      ((schemeSpaceFunctor B S hS).map (specSiteObjectMap ι field_mem₁ ring_mem₃ _) ≫
        (schemeSpaceFunctor B S hS).map (specSiteObjectMap (algebraMap R₁ K₁) ring_mem₁
          field_mem₁ base₁) ≫ h₁)
      ((schemeSpaceFunctor B S hS).map (specSiteObjectMap (algebraMap A K₃) ring_mem₄
          field_mem₃ (Spec.map (CommRingCat.ofHom (φ₄.comp φ₁)) ≫ base)) ≫
        (schemeSpaceFunctor B S hS).map (specSiteObjectMap (φ₄.comp φ₁) ring_mem ring_mem₄
          base) ≫ h) (by
      simp only [h₁, ← Functor.map_comp_assoc]
      congr 2
      exact siteObject_hom_ext (by
        simp only [Functor.map_comp, Over.comp_left, inclusion_map_specSiteObjectHom_left,
          inclusion_map_specSiteObjectMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl))
    have hm' : valuationRingExtensionHom (algebraMap A K₃) ring_mem₄ field_mem₃
        (Spec.map (CommRingCat.ofHom (φ₄.comp φ₁)) ≫ base) _ ≫ g₄ = m' ≫ g₃ ≫ gK₁ :=
      testScheme_hom_ext (by
        simp only [CostructuredArrow.comp_left, Over.comp_left, Functor.map_comp, g₄, g₃, gK₁,
          m', testSchemeHom, CostructuredArrow.homMk_left, valuationRingExtensionHom,
          inclusion_map_specSiteObjectHom_left, inclusion_map_specSiteObjectMap_left,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl)
    have e : ∀ M : s.picardAt (CostructuredArrow.mk h₁),
        s.picardMap (valuationRingExtensionHom (algebraMap A K₃) ring_mem₄ field_mem₃
          (Spec.map (CommRingCat.ofHom (φ₄.comp φ₁)) ≫ base) _) (s.picardMap g₄ M) =
        s.picardMap m' (s.picardMap g₃ (s.picardMap gK₁ M)) := fun M =>
      (s.picardMap_comp _ g₄ M).symm.trans ((congrArg (fun k => s.picardMap k M) hm').trans
        ((s.picardMap_comp m' (g₃ ≫ gK₁) M).trans
          (congrArg (s.picardMap m') (s.picardMap_comp g₃ gK₁ M))))
    exact (e L₁).trans ((congrArg (s.picardMap m') h₃).trans (e N₁).symm)

end PicardSituation

end AlgebraicGeometry.Space

end
