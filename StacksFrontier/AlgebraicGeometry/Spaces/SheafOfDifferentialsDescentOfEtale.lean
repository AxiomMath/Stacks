module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparison

/-!
# The descent isomorphism of the sheaf of differentials for étale legs

Let `pX : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `π : U ⟶ X` be a
presentation and let `s, t : R ⟶ U` be *étale* with `s ≫ π = t ≫ π`, the situation of an étale
presentation with `R = U ×_X U`.  Writing `p` for `U ⟶ Y` and `q` for `R ⟶ Y`, the comparison
maps `c_s : s^*Ω_{U/Y} ⟶ Ω_{R/Y}` and `c_t : t^*Ω_{U/Y} ⟶ Ω_{R/Y}` of Stacks 04CX are
isomorphisms, which is the étale-localization clause of Stacks 04CU in the form
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale`.  Their composite `α`,
namely `c_s` followed by the inverse of `c_t`, is the descent isomorphism
`s^*Ω_{U/Y} ≅ t^*Ω_{U/Y}` of Stacks 04CW.  It satisfies the cocycle condition — the check the
source leaves to the reader — and it is the transition isomorphism of the canonical descent
datum of Stacks 04W5, so the module `α` descends to is `Ω_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale` is the descent isomorphism `α`
  of Stacks 04CW, built from the two comparison maps of Stacks 04CX for two étale legs `s, t`.

## Main results

* `AlgebraicGeometry.Space.eq_sheafOfDifferentialsDescentIsoOfEtale_hom`: `α` is the unique
  morphism whose composite with `c_t` is `c_s`.
* `AlgebraicGeometry.Space.pullbackComparison_sheafOfDifferentialsDescentIsoOfEtale`: pulling `α`
  back along a morphism into `R` and normalizing by the comparisons of iterated inverse images
  gives the descent isomorphism of the two resulting legs.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_trans`: the descent isomorphisms
  of three étale legs over `U` compose.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_cocycle`: **`α` satisfies the
  cocycle condition**, on a test space carrying three compatible legs — the three projections of
  a triple fibre product.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_canonicalComparison`: **`α` is
  the transition isomorphism of the canonical descent datum of `Ω_{X/Y}`**, so the module `α`
  descends to is `Ω_{X/Y}`.
* `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_canonicalDescentDatum_transition`:
  the same statement read in the vocabulary of Stacks 04W5, about the descent datum
  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` itself.

## Implementation notes

Invertibility of `c_s` and `c_t` is *derived* from étaleness of `s` and `t` by
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale`, which identifies a
comparison map of Stacks 04CX for a triangle over `Y` with the étale-source localization
isomorphism `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`.  None of
the statements here assumes invertibility; the identity `α` is divided out of,
`AlgebraicGeometry.Space.canonicalComparison_comp_sheafOfDifferentialsMap`, needs neither
étaleness nor invertibility.  `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso` is the
same composite for a caller which holds the two isomorphisms and no étaleness.

The descent isomorphism `α` and the statements about it are formed from the comparison maps
`AlgebraicGeometry.Space.sheafOfDifferentialsMap` of the relevant commuting squares, which have
the characterizing property of Stacks 04CX by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap`; no comparison map
and no invertibility is an input.  The auxiliary identities
`AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_hom_comp` and
`AlgebraicGeometry.Space.eq_sheafOfDifferentialsDescentIsoOfEtale_hom` accept any morphisms with
the characterizing property, which by uniqueness are those comparison maps.

The cocycle condition is read on a test space carrying three compatible legs to `U` — the
three projections of a triple fibre product — and the pullback of `α` along a leg is
normalized by `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison`, the
identification of `g^*s^*Ω_{U/Y}` with `(g ≫ s)^*Ω_{U/Y}`.  That is the same normalization the
cocycle field of `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` uses, through
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn`.

## References

* [Stacks Project, Tag 04CW](https://stacks.math.columbia.edu/tag/04CW)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7), the comparison maps of
  two stacked squares compose.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), étale localization of
  the sheaf of differentials.
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5), the canonical descent
  datum of a quasi-coherent module.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y U R : AlgebraicSpaces B S hS}

/-- **Stacks 04CW.** The descent isomorphism `α : s^*Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t^*Ω_{U/Y}` attached to
two *étale* morphisms `s, t : R ⟶ U` of algebraic spaces inducing the same morphism `q : R ⟶ Y`.

It is the comparison map `c_s` of Stacks 04CX for the triangle `s ≫ p = q`, namely
`AlgebraicGeometry.Space.sheafOfDifferentialsMap`, followed by the inverse of the comparison map
`c_t` of the triangle `t ≫ p = q`.  Both comparison maps are isomorphisms because `s` and `t`
are étale: that is the étale-localization clause of Stacks 04CU, in the form
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale`. -/
@[stacks 04CW "the descent isomorphism itself: `alpha : s^*Omega_{U/Y} -> t^*Omega_{U/Y}`, \
built from the two etale projections of the groupoid"]
def sheafOfDifferentialsDescentIsoOfEtale (p : U ⟶ Y) {s t : R ⟶ U} {q : R ⟶ Y}
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q) :
    (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ≅
      (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) :=
  @asIso _ _ _ _ (sheafOfDifferentialsMap B S hS s p q (𝟙 Y) (by rw [hsq, Category.comp_id]))
      (isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS s hs p q hsq
        (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS s p q (𝟙 Y) _)) ≪≫
    (@asIso _ _ _ _ (sheafOfDifferentialsMap B S hS t p q (𝟙 Y) (by rw [htq, Category.comp_id]))
      (isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS t ht p q htq
        (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS t p q (𝟙 Y) _))).symm

/-- The comparison map of a triangle `u ≫ p = q` over `𝟙 Y` has the characterizing property. -/
private theorem isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq {u : R ⟶ U}
    {p : U ⟶ Y} {q : R ⟶ Y} (h : u ≫ p = q) :
    IsSheafOfDifferentialsMap B S hS u p q
      (sheafOfDifferentialsMap B S hS u p q (𝟙 Y) (by rw [h, Category.comp_id])) :=
  isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS u p q (𝟙 Y) _

/-- The defining property of the descent isomorphism `α`: composed with a comparison map `c_t`
of Stacks 04CX it is the comparison map `c_s`.  Any morphisms with the characterizing property
may be used, since by `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` there is only
one of each. -/
theorem sheafOfDifferentialsDescentIsoOfEtale_hom_comp (p : U ⟶ Y) {s t : R ⟶ U} {q : R ⟶ Y}
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q)
    {cs : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    {ct : (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    (hcs : IsSheafOfDifferentialsMap B S hS s p q cs)
    (hct : IsSheafOfDifferentialsMap B S hS t p q ct) :
    (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom ≫ ct = cs := by
  rw [eq_of_isSheafOfDifferentialsMap B S hS s p q hcs
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hsq),
    eq_of_isSheafOfDifferentialsMap B S hS t p q hct
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS htq)]
  simp [sheafOfDifferentialsDescentIsoOfEtale]

/-- **The descent isomorphism is the unique morphism `s^*Ω_{U/Y} ⟶ t^*Ω_{U/Y}` compatible with
the two comparison maps to `Ω_{R/Y}`.** -/
theorem eq_sheafOfDifferentialsDescentIsoOfEtale_hom (p : U ⟶ Y) {s t : R ⟶ U} {q : R ⟶ Y}
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q)
    {cs : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    {ct : (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    (hcs : IsSheafOfDifferentialsMap B S hS s p q cs)
    (hct : IsSheafOfDifferentialsMap B S hS t p q ct)
    {φ : (modulePullback B S hS s).obj (sheafOfDifferentials B S hS p) ⟶
      (modulePullback B S hS t).obj (sheafOfDifferentials B S hS p)}
    (hφ : φ ≫ ct = cs) :
    φ = (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom := by
  have : IsIso ct := isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS t ht p q htq hct
  rw [← cancel_mono ct, hφ,
    sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p hs ht hsq htq hcs hct]

/-- **The descent isomorphisms of three étale legs over `U` compose.**  All three are built out
of the comparison maps to `Ω_{R/Y}`, so the middle one cancels. -/
theorem sheafOfDifferentialsDescentIsoOfEtale_trans (p : U ⟶ Y) {a₀ a₁ a₂ : R ⟶ U} {q : R ⟶ Y}
    (h₀ : IsEtale B S hS a₀.hom) (h₁ : IsEtale B S hS a₁.hom) (h₂ : IsEtale B S hS a₂.hom)
    (hq₀ : a₀ ≫ p = q) (hq₁ : a₁ ≫ p = q) (hq₂ : a₂ ≫ p = q) :
    sheafOfDifferentialsDescentIsoOfEtale B S hS p h₀ h₁ hq₀ hq₁ ≪≫
        sheafOfDifferentialsDescentIsoOfEtale B S hS p h₁ h₂ hq₁ hq₂ =
      sheafOfDifferentialsDescentIsoOfEtale B S hS p h₀ h₂ hq₀ hq₂ := by
  have hc₀ := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hq₀
  have hc₁ := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hq₁
  have hc₂ := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hq₂
  have := isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS a₂ h₂ p q hq₂ hc₂
  ext1
  rw [← cancel_mono (sheafOfDifferentialsMap B S hS a₂ p q (𝟙 Y) _), Iso.trans_hom,
    Category.assoc, sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p h₁ h₂ hq₁ hq₂ hc₁ hc₂,
    sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p h₀ h₁ hq₀ hq₁ hc₀ hc₁,
    sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p h₀ h₂ hq₀ hq₂ hc₀ hc₂]

/-- **Precomposing a triangle over `Y` with a further morphism does not change its comparison
map of Stacks 04CX**, once the inverse image is normalized by the comparison of iterated
inverse images: the comparison map of `u : R ⟶ U` pulled back along `g : T ⟶ R` and followed
by the comparison map of `g` is the comparison map of `g ≫ u`.

This is Stacks 05Z7 in the form
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp`, transported along `g ≫ u = a` and
divided out by the uniqueness clause of Stacks 04CX. -/
theorem pullbackComparison_hom_comp_sheafOfDifferentialsMap {T : AlgebraicSpaces B S hS}
    (p : U ⟶ Y) (u : R ⟶ U) (q : R ⟶ Y) (g : T ⟶ R) {a : T ⟶ U} (r : T ⟶ Y)
    (hgu : g ≫ u = a)
    {cu : (modulePullback B S hS u).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS q}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q) ⟶
      sheafOfDifferentials B S hS r}
    {ca : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS r}
    (hcu : IsSheafOfDifferentialsMap B S hS u p q cu)
    (hcg : IsSheafOfDifferentialsMap B S hS g q r cg)
    (hca : IsSheafOfDifferentialsMap B S hS a p r ca) :
    (QuasiCoherentDescent.pullbackComparison B S hS g u a hgu
          (sheafOfDifferentials B S hS p)).hom ≫
        (modulePullback B S hS g).map cu ≫ cg = ca := by
  subst hgu
  rw [QuasiCoherentDescent.pullbackComparison_rfl]
  simp only [Iso.symm_hom, Iso.app_inv]
  exact eq_of_isSheafOfDifferentialsMap B S hS (g ≫ u) p r
    (isSheafOfDifferentialsMap_comp B S hS u g p q r hcu hcg) hca

/-- **The pullback of the descent isomorphism along a morphism into `R` is the descent
isomorphism of the two resulting legs.**  The legs `a = g ≫ s` and `b = g ≫ t` are required to
be étale, and the normalization is by the comparisons `g^*s^*Ω_{U/Y} ≅ a^*Ω_{U/Y}` and
`g^*t^*Ω_{U/Y} ≅ b^*Ω_{U/Y}` of iterated inverse images. -/
theorem pullbackComparison_sheafOfDifferentialsDescentIsoOfEtale {T : AlgebraicSpaces B S hS}
    (p : U ⟶ Y) {s t : R ⟶ U} (q : R ⟶ Y)
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q) (g : T ⟶ R) {a b : T ⟶ U} (r : T ⟶ Y)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hga : g ≫ s = a) (hgb : g ≫ t = b) (har : a ≫ p = r) (hbr : b ≫ p = r) :
    (QuasiCoherentDescent.pullbackComparison B S hS g s a hga
          (sheafOfDifferentials B S hS p)).hom ≫
        (modulePullback B S hS g).map
          (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom ≫
        (QuasiCoherentDescent.pullbackComparison B S hS g t b hgb
          (sheafOfDifferentials B S hS p)).inv =
      (sheafOfDifferentialsDescentIsoOfEtale B S hS p ha hb har hbr).hom := by
  have hgr : g ≫ q = r ≫ 𝟙 Y := by rw [← hsq, ← Category.assoc, hga, har, Category.comp_id]
  have hcs := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hsq
  have hct := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS htq
  have hcg := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS g q r (𝟙 Y) hgr
  have hca := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS har
  have hcb := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hbr
  have hA := pullbackComparison_hom_comp_sheafOfDifferentialsMap B S hS p s q g r hga
    hcs hcg hca
  have hB := pullbackComparison_hom_comp_sheafOfDifferentialsMap B S hS p t q g r hgb
    hct hcg hcb
  refine eq_sheafOfDifferentialsDescentIsoOfEtale_hom B S hS p ha hb har hbr hca hcb ?_
  rw [← hA, ← hB]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((modulePullback B S hS g).map
      (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom),
    ← Functor.map_comp,
    sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p hs ht hsq htq hcs hct]

/-- **Stacks 04CW**, the cocycle condition.  Let the test space `T` carry three étale legs
`a₀, a₁, a₂ : T ⟶ U` over `Y` and three morphisms `g₀₁, g₁₂, g₀₂ : T ⟶ R` realizing the pairs
`(a₀, a₁)`, `(a₁, a₂)` and `(a₀, a₂)` through `(s, t)` — the situation of the three projections
of a triple fibre product.  Then the pullback of `α` along `g₀₂` is the composite of its
pullbacks along `g₀₁` and `g₁₂`, each normalized by the comparisons of iterated inverse images.
So `α` is a descent datum, which is the check the source leaves to the reader. -/
@[stacks 04CW "the cocycle condition for that isomorphism, which is what the remark leaves to \
the reader to verify"]
theorem sheafOfDifferentialsDescentIsoOfEtale_cocycle {T : AlgebraicSpaces B S hS} (p : U ⟶ Y)
    {s t : R ⟶ U} (q : R ⟶ Y)
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q) (g₀₁ g₁₂ g₀₂ : T ⟶ R) {a₀ a₁ a₂ : T ⟶ U} (r : T ⟶ Y)
    (h₀ : IsEtale B S hS a₀.hom) (h₁ : IsEtale B S hS a₁.hom) (h₂ : IsEtale B S hS a₂.hom)
    (h₀₁s : g₀₁ ≫ s = a₀) (h₀₁t : g₀₁ ≫ t = a₁) (h₁₂s : g₁₂ ≫ s = a₁)
    (h₁₂t : g₁₂ ≫ t = a₂) (h₀₂s : g₀₂ ≫ s = a₀) (h₀₂t : g₀₂ ≫ t = a₂)
    (hr₀ : a₀ ≫ p = r) (hr₁ : a₁ ≫ p = r) (hr₂ : a₂ ≫ p = r) :
    (QuasiCoherentDescent.pullbackComparison B S hS g₀₂ s a₀ h₀₂s
          (sheafOfDifferentials B S hS p)).hom ≫
        (modulePullback B S hS g₀₂).map
          (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom ≫
        (QuasiCoherentDescent.pullbackComparison B S hS g₀₂ t a₂ h₀₂t
          (sheafOfDifferentials B S hS p)).inv =
      ((QuasiCoherentDescent.pullbackComparison B S hS g₀₁ s a₀ h₀₁s
            (sheafOfDifferentials B S hS p)).hom ≫
          (modulePullback B S hS g₀₁).map
            (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom ≫
          (QuasiCoherentDescent.pullbackComparison B S hS g₀₁ t a₁ h₀₁t
            (sheafOfDifferentials B S hS p)).inv) ≫
        ((QuasiCoherentDescent.pullbackComparison B S hS g₁₂ s a₁ h₁₂s
            (sheafOfDifferentials B S hS p)).hom ≫
          (modulePullback B S hS g₁₂).map
            (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom ≫
          (QuasiCoherentDescent.pullbackComparison B S hS g₁₂ t a₂ h₁₂t
            (sheafOfDifferentials B S hS p)).inv) := by
  rw [pullbackComparison_sheafOfDifferentialsDescentIsoOfEtale B S hS p q hs ht hsq htq g₀₂ r h₀ h₂
      h₀₂s h₀₂t hr₀ hr₂,
    pullbackComparison_sheafOfDifferentialsDescentIsoOfEtale B S hS p q hs ht hsq htq g₀₁ r h₀ h₁
      h₀₁s h₀₁t hr₀ hr₁,
    pullbackComparison_sheafOfDifferentialsDescentIsoOfEtale B S hS p q hs ht hsq htq g₁₂ r h₁ h₂
      h₁₂s h₁₂t hr₁ hr₂,
    ← sheafOfDifferentialsDescentIsoOfEtale_trans B S hS p h₀ h₁ h₂ hr₀ hr₁ hr₂]
  rfl

/-- **Stacks 04CW.** For a presentation `π : U ⟶ X` of an algebraic space `X` over `Y`, with
`p = π ≫ pX`, and étale `s, t : R ⟶ U` with `s ≫ π = t ≫ π` inducing the same morphism
`q : R ⟶ Y`, the descent isomorphism `α` is the transition isomorphism of the canonical descent
datum of `Ω_{X/Y}`: the comparison map `c_π : π^*Ω_{X/Y} ⟶ Ω_{U/Y}` of Stacks 04CX, namely
`AlgebraicGeometry.Space.sheafOfDifferentialsMap`, carries the canonical comparison of the two
inverse images of `Ω_{X/Y}` to `α`.  When `π` is étale `c_π` is an isomorphism, by
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale`, so for a presentation
the module `α` descends to is `Ω_{X/Y}`; étaleness of `π` is not needed for the identity itself
and is not assumed.

The identity `α` is divided out of,
`AlgebraicGeometry.Space.canonicalComparison_comp_sheafOfDifferentialsMap`, needs no
invertibility; the invertibility of `c_s` and `c_t` that forms `α` is derived from étaleness of
`s` and `t` by Stacks 04CU.

The cocycle condition is the separate statement
`AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_cocycle` above, and in the
scheme-level vocabulary `AlgebraicGeometry.Scheme.Hom.differentialsDescentIso_cocycle` in
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/EtaleDescentDatum.lean`.  Together with
`AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale` and that cocycle condition, this
is the source's remark in the vocabulary of algebraic spaces: the module obtained by gluing
`Ω_{U/Y}` along `α` is `Ω_{X/Y}`. -/
@[stacks 04CW "the module `α` descends to is `Ω_{X/Y}`: `α` is the transition isomorphism of \
the canonical descent datum of `Ω_{X/Y}` on a presentation `π : U ⟶ X` which the two étale \
projections equalize"]
theorem sheafOfDifferentialsDescentIsoOfEtale_canonicalComparison (pX : X ⟶ Y) (π : U ⟶ X)
    (p : U ⟶ Y) {s t : R ⟶ U} (q : R ⟶ Y) (hπ : s ≫ π = t ≫ π) (hπp : π ≫ pX = p)
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom) (hsq : s ≫ p = q)
    (htq : t ≫ p = q) :
    (QuasiCoherentDescent.canonicalComparison s t π π hπ
          (sheafOfDifferentials B S hS pX)).hom ≫
        (modulePullback B S hS t).map
          (sheafOfDifferentialsMap B S hS π pX p (𝟙 Y) (by rw [hπp, Category.comp_id])) =
      (modulePullback B S hS s).map
          (sheafOfDifferentialsMap B S hS π pX p (𝟙 Y) (by rw [hπp, Category.comp_id])) ≫
        (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom := by
  have hcπ := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hπp
  have hcs := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS hsq
  have hct := isSheafOfDifferentialsMap_sheafOfDifferentialsMap_of_comp_eq B S hS htq
  have := isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS t ht p q htq hct
  rw [← cancel_mono (sheafOfDifferentialsMap B S hS t p q (𝟙 Y) _), Category.assoc,
    Category.assoc, sheafOfDifferentialsDescentIsoOfEtale_hom_comp B S hS p hs ht hsq htq hcs hct]
  exact canonicalComparison_comp_sheafOfDifferentialsMap B S hS pX π p q hπ hcπ hcs hct

/-- **Stacks 04CW in the vocabulary of Stacks 04W5.**  `α` is the transition isomorphism, at the
`i`-th pairwise fibre product, of the canonical descent datum of `Ω_{X/Y}` relative to a family
`(π j : V j ⟶ X)` of algebraic spaces over `X`: the module `α` descends to is `Ω_{X/Y}`.

This is `AlgebraicGeometry.Space.sheafOfDifferentialsDescentIsoOfEtale_canonicalComparison`
read through `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum_transition`; the
extra input `hM` is the one needed to form a canonical descent datum at all, and is the standing
hypothesis of `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum`. -/
theorem sheafOfDifferentialsDescentIsoOfEtale_canonicalDescentDatum_transition (pX : X ⟶ Y)
    {I : Type v} (V : I → AlgebraicSpaces B S hS) (π : ∀ j, V j ⟶ X)
    (hM : (sheafOfDifferentials B S hS pX).IsQuasicoherentOnSite) (i : I) (p : V i ⟶ Y)
    (hπp : π i ≫ pX = p) (q : QuasiCoherentDescent.pair B S hS V π i i ⟶ Y)
    (hs : IsEtale B S hS (QuasiCoherentDescent.pairFst B S hS V π i i).hom)
    (ht : IsEtale B S hS (QuasiCoherentDescent.pairSnd B S hS V π i i).hom)
    (hsq : QuasiCoherentDescent.pairFst B S hS V π i i ≫ p = q)
    (htq : QuasiCoherentDescent.pairSnd B S hS V π i i ≫ p = q) :
    ((QuasiCoherentDescent.canonicalDescentDatum B S hS V π
            (sheafOfDifferentials B S hS pX) hM).transition i i).hom ≫
        (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS V π i i)).map
          (sheafOfDifferentialsMap B S hS (π i) pX p (𝟙 Y) (by rw [hπp, Category.comp_id])) =
      (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS V π i i)).map
          (sheafOfDifferentialsMap B S hS (π i) pX p (𝟙 Y) (by rw [hπp, Category.comp_id])) ≫
        (sheafOfDifferentialsDescentIsoOfEtale B S hS p hs ht hsq htq).hom := by
  rw [QuasiCoherentDescent.canonicalDescentDatum_transition]
  exact sheafOfDifferentialsDescentIsoOfEtale_canonicalComparison B S hS pX (π i) p q
    (QuasiCoherentDescent.pair_condition B S hS V π i i) hπp hs ht hsq htq

end AlgebraicGeometry.Space

end
