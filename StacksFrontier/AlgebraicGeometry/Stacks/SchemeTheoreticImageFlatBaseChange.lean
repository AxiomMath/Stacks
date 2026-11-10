module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of the scheme theoretic image of a morphism of algebraic stacks (Stacks 0CMK)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S` and let `b : 𝒴' ⟶ 𝒴`
be flat. **Stacks 0CMK** says that formation of the scheme theoretic image (Stacks 0CMI, which
exists by Stacks 0CPU) commutes with the base change along `b`: the scheme theoretic image of the
base change `f' : 𝒳 ×_𝒴 𝒴' ⟶ 𝒴'` is the inverse image under `b` of the scheme theoretic image of
`f`.

## Main definitions

* `AlgebraicGeometry.Stack.chartImageSubfunctor`: for `v : (Sch/V)_fppf ⟶ 𝒴`, the scheme-theoretic
  image in `V` of the base change `𝒳 ×_𝒴 V ⟶ V`, as the smallest closed subspace of `V`
  containing the morphisms `T ⟶ V` which lift to `𝒳 ×_𝒴 V`.
* `AlgebraicGeometry.Stack.flatLocalImage`: the property of the objects of `𝒴` cut out by the
  chart images along all smooth charts by affine objects of the site.

## Main results

* `AlgebraicGeometry.Stack.isSchemeTheoreticImage_inverseImage_of_isFlat`: **Stacks 0CMK**.
* `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_twoFibreProduct_fst`: the same, as an
  equality of the intersections of Stacks 0CPU.
* `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_le_inverseImage`,
  `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_inverseImage_fullSubcategoryInclusion`
  and `AlgebraicGeometry.Stack.isSchemeTheoreticImage_inverseImage_of_flatFactorization`: one
  containment for any 2-commutative square, the case of the inclusion of a closed substack, and
  the case of a base change factoring flatly onto the preimage of the image.
* `AlgebraicGeometry.Stack.chartImageSubfunctor_le_schemeTheoreticImageSubfunctor`: the chart
  image lies in the scheme-theoretic image of a smooth surjective presentation of `𝒳 ×_𝒴 V`
  composed with the projection to `V`.
* `AlgebraicGeometry.Stack.preimage_chartImageSubfunctor_le`: flat base change of chart images
  along a flat morphism of the site, for a chart by an affine object, from Stacks 089E/081I.
* `AlgebraicGeometry.Stack.chartImageSubfunctor_le_chartSubfunctor_flatLocalImage`: the chart
  images of the smooth affine charts are invariant, the claim of the source's proof of (a).
* `AlgebraicGeometry.Stack.isClosedSubstack_flatLocalImage`: the flat-local image of a
  quasi-compact `f` is a closed substack of `𝒴`, through which `f` factors.
* `AlgebraicGeometry.Stack.inverseImage_flatLocalImage_le`: its inverse image under a flat `b`
  lies in the scheme theoretic image of the base change.

## The proof

The source's. For a smooth chart `V ⟶ 𝒴` by an affine `V`, the base change `𝒳 ×_𝒴 V` is
quasi-compact and so has a smooth surjective presentation by an affine `A` (Stacks 04YC); the
chart image is the scheme-theoretic image of `A ⟶ V` (Stacks 0CMJ in the form of Stacks 06QA),
and therefore commutes with flat base change of `V` (Stacks 081I, read on subfunctors as in
Stacks 089E). This gives, first, that the chart images of two smooth affine charts agree on a
smooth presentation of the 2-fibre product of the two charts — the `R`-invariance of the source's
step (a) — so that they descend to a closed substack of `𝒴` by Stacks 0507
(`AlgebraicGeometry.Stack.isClosedSubstack_of_isClosedSubspace_chartSubfunctor`); that substack,
the flat-local image, contains the scheme theoretic image of `f` because `f` factors through it.
Second, with `𝒴'` covered by smooth presentations `E` of the 2-fibre products `V ×_𝒴 𝒴'`, whose
projections `E ⟶ V` are flat because `b` is, the same flat base change shows that the inverse
image of the flat-local image is contained, on every such chart, in the scheme theoretic image of
`f'` — the source's steps (b) and (c). The other containment holds for any 2-commutative square.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CMJ](https://stacks.math.columbia.edu/tag/0CMJ)
* [Stacks Project, Tag 0CMK](https://stacks.math.columbia.edu/tag/0CMK)
* [Stacks Project, Tag 0CPU](https://stacks.math.columbia.edu/tag/0CPU)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/
@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section TwoIso

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- Factoring through a strictly full subcategory of the target is invariant under 2-isomorphism
of 1-morphisms: both sides are conditions on the objects in the image, and a 2-isomorphism
supplies an isomorphism between the two images of each object. -/
public theorem factorsThroughSubstack_of_twoIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    {Q : ObjectProperty 𝒴.val.val.obj} [Q.IsClosedUnderIsomorphisms]
    (h : FactorsThroughSubstack f Q) : FactorsThroughSubstack g Q := by
  rw [factorsThroughSubstack_iff_forall] at h ⊢
  exact fun X => Q.prop_of_iso
    ((CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS e)).app X) (h X)

/-- Being the scheme theoretic image is invariant under 2-isomorphism of 1-morphisms, both the
factorization clause and the minimality clause being so by
`AlgebraicGeometry.Stack.factorsThroughSubstack_of_twoIso`. -/
public theorem isSchemeTheoreticImage_of_twoIso {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    {P : ObjectProperty 𝒴.val.val.obj} (h : IsSchemeTheoreticImage f P) :
    IsSchemeTheoreticImage g P := by
  have := h.1.1
  refine ⟨h.1, factorsThroughSubstack_of_twoIso e h.2.1, fun Q hQ hfac => ?_⟩
  have := hQ.1
  exact h.2.2 Q hQ (factorsThroughSubstack_of_twoIso e.symm hfac)

end TwoIso

section InverseImageSquare

variable {𝒴₁ 𝒴₂ : AlgebraicStacks.{u, w} B S hS}

/-- The leg over `𝒴₁` of the square exhibiting the preimage of a substack as a base change is the
inclusion of that preimage. -/
public theorem inverseImageSquare_fst (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    (inverseImageSquare b P hPalg).fst =
      fullSubcategoryInclusion 𝒴₁ (P.inverseImage b.hom.hom.toFunctor)
        (isAlgebraicStack_inverseImage b P hPalg) :=
  rfl

end InverseImageSquare

section BaseChange

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **The easy containment of Stacks 0CMK, for any 2-commutative square.** Let `f : 𝒳 ⟶ 𝒴` and
`b : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` and let `sq` be a 2-commutative square
over them, with
apex `sq.pt` and legs `sq.fst : sq.pt ⟶ 𝒴'` and `sq.snd : sq.pt ⟶ 𝒳`. Then the intersection of
the closed substacks of `𝒴'` through which `sq.fst` factors is contained in the preimage under
`b` of the intersection of the closed substacks of `𝒴` through which `f` factors.

Let `Q` be a closed substack of `𝒴` through which `f` factors. Its preimage under `b` is a closed
substack of `𝒴'` (`AlgebraicGeometry.Stack.isClosedSubstack_inverseImage`) through which `sq.fst`
factors (`AlgebraicGeometry.Stack.factorsThroughSubstack_inverseImage`, which is where the
2-commutativity of the square is used), so the candidate image of `sq.fst` is contained in it by
its own minimality. As `Q` ranges over the closed substacks of `𝒴` through which `f` factors this
says exactly that an object of the candidate image of `sq.fst` has its image under `b` in the
candidate image of `f`. -/
@[stacks 0CMK "containment"]
public theorem schemeTheoreticImageCandidate_le_inverseImage (f : 𝒳 ⟶ 𝒴) (b : 𝒴' ⟶ 𝒴)
    (sq : Bicategory.TwoCommSq b f) :
    schemeTheoreticImageCandidate sq.fst ≤
      (schemeTheoreticImageCandidate f).inverseImage b.hom.hom.toFunctor := by
  intro X hX
  change schemeTheoreticImageCandidate f (b.hom.hom.toFunctor.obj X)
  rw [schemeTheoreticImageCandidate_apply_iff]
  intro Q hQ hfac
  have := hQ.1
  exact schemeTheoreticImageCandidate_le sq.fst (Q := Q.inverseImage b.hom.hom.toFunctor)
    (isClosedSubstack_inverseImage b hQ) (factorsThroughSubstack_inverseImage sq.iso hfac) X hX

/-- **Stacks 0CMK for the inclusion of a closed substack.** Let `P` cut out a closed substack of
`𝒴₂` and let `b : 𝒴₁ ⟶ 𝒴₂` be any 1-morphism of algebraic stacks over `S`. The base change of the
inclusion of that substack along `b` is the inclusion of the preimage of `P`, by
`AlgebraicGeometry.Stack.inverseImageSquare_fst`, and the square realising it is a 2-fibre product
by `AlgebraicGeometry.Stack.isTwoFibreProduct_inverseImageSquare`. Then the scheme theoretic image
of that base change is the preimage under `b` of the scheme theoretic image of the inclusion.

Both sides are computed by
`AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_fullSubcategoryInclusion`: a closed
substack is the scheme theoretic image of its own inclusion, and the preimage of a closed substack
is a closed substack. Neither flatness of `b` nor quasi-compactness of the inclusion is used. -/
@[stacks 0CMK "closed_substack_case"]
public theorem schemeTheoreticImageCandidate_inverseImage_fullSubcategoryInclusion
    {𝒴₁ 𝒴₂ : AlgebraicStacks.{u, w} B S hS} (b : 𝒴₁ ⟶ 𝒴₂)
    {P : ObjectProperty 𝒴₂.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hP : IsClosedSubstack 𝒴₂ P)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    schemeTheoreticImageCandidate (inverseImageSquare b P hPalg).fst =
      (schemeTheoreticImageCandidate (fullSubcategoryInclusion 𝒴₂ P hPalg)).inverseImage
        b.hom.hom.toFunctor := by
  rw [inverseImageSquare_fst, schemeTheoreticImageCandidate_fullSubcategoryInclusion _ _ hP]
  exact schemeTheoreticImageCandidate_fullSubcategoryInclusion _
    (isAlgebraicStack_inverseImage b P hPalg) (isClosedSubstack_inverseImage b hP)

/-- **Stacks 0CMK**, assuming the base change covers the preimage substack flatly. Let
`f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S`, let `b : 𝒴' ⟶ 𝒴` be flat,
let `sq` be a 2-commutative square over them and let `P` be the scheme theoretic image of `f`.
Suppose `sq.fst` factors, up to a 2-isomorphism, as a surjective, flat 1-morphism `k` locally of
finite presentation onto the preimage of `P` under `b`, followed by the inclusion of that
preimage. Then the preimage of `P` under `b` is the scheme theoretic image of `sq.fst`.

The preimage of `P` is a closed substack of `𝒴'`
(`AlgebraicGeometry.Stack.isClosedSubstack_inverseImage`), hence is the scheme theoretic image of
its own inclusion; `k` being surjective, flat and locally of finite presentation, **Stacks 0CMJ**
in the form `AlgebraicGeometry.Stack.isSchemeTheoreticImage_comp_iff` transfers that to
`k` followed by the inclusion, and
`AlgebraicGeometry.Stack.isSchemeTheoreticImage_of_twoIso` transports it along the given
2-isomorphism to `sq.fst`.

This is the shape in which the source's argument delivers the conclusion, the covering `k` being
produced from atlases; but the existence of such a `k` is a genuine extra hypothesis, not a
consequence of the conclusion, and quasi-compactness of `f` and flatness of `b` are carried
without being used. The statement with no factorization is
`AlgebraicGeometry.Stack.isSchemeTheoreticImage_inverseImage_of_isFlat`. -/
public theorem isSchemeTheoreticImage_inverseImage_of_flatFactorization (f : 𝒳 ⟶ 𝒴)
    (b : 𝒴' ⟶ 𝒴) (sq : Bicategory.TwoCommSq b f) (_hf : IsQuasiCompactMorphism B S hS f)
    (_hb : AlgebraicStacks.IsFlat B S hS b) {P : ObjectProperty 𝒴.val.val.obj}
    (hP : IsSchemeTheoreticImage f P)
    (hA : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒴' (P.inverseImage b.hom.hom.toFunctor)))
    (k : sq.pt ⟶ fullSubcategoryAlgebraicStack 𝒴' (P.inverseImage b.hom.hom.toFunctor) hA)
    (hk : k ≫ fullSubcategoryInclusion 𝒴' (P.inverseImage b.hom.hom.toFunctor) hA ≅ sq.fst)
    (hsurj : IsSurjective B S hS k) (hflat : AlgebraicStacks.IsFlat B S hS k)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS k) :
    IsSchemeTheoreticImage sq.fst (P.inverseImage b.hom.hom.toFunctor) := by
  have := (isClosedSubstack_inverseImage b hP.1).1
  exact isSchemeTheoreticImage_of_twoIso hk ((isSchemeTheoreticImage_comp_iff
      (fullSubcategoryInclusion 𝒴' (P.inverseImage b.hom.hom.toFunctor) hA) k hsurj hflat hlfp).1
    (isSchemeTheoreticImage_fullSubcategoryInclusion _ hA (isClosedSubstack_inverseImage b hP.1)))

end BaseChange

section ChartImage

open CategoryTheory.Limits Opposite

/-- **Reading a base equation off a morphism of `(Sch/V)_fppf`.** A morphism
`Over.mk a ⟶ Over.mk b` of the slice over `V` lying over `k` in the big fppf site says
`k ≫ b = a`. -/
theorem comp_eq_of_isHomLift_over {V T T' : BigFppfOver B S hS} {a : T' ⟶ V} {b : T ⟶ V}
    (k : T' ⟶ T) (m : (Over.mk a : Over V) ⟶ Over.mk b) (hm : (Over.forget V).IsHomLift k m) :
    k ≫ b = a := by
  rw [@IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget V) (Over.mk a) (Over.mk b) k m hm]
  exact Over.w m

/-- **Reading a projection of a lift off a morphism of the site.** Let `c : (Sch/E)_fppf ⟶ 𝒵`
and `π : 𝒵 ⟶ (Sch/V)_fppf`, let `ξ` be an object of `𝒵` with `π ξ = s` for `s : T ⟶ V`, and
let `α : c(ε) ⟶ ξ` lie over `k`. Then `k ≫ s` is `ε` followed by the morphism of the site
underlying `c ≫ π`. -/
theorem comp_eq_siteMap_of_isHomLift {𝒵 : AlgebraicStacks.{u, w} B S hS}
    {E V T : BigFppfOver B S hS} (c : schemeStack.{u, w} B S hS E ⟶ 𝒵)
    (π : 𝒵 ⟶ schemeStack.{u, w} B S hS V) {s : T ⟶ V} {ξ : 𝒵.val.val.obj}
    (hξ : π.hom.hom.obj ξ = Over.mk s) (ε : Over E) (k : ε.left ⟶ T)
    (α : c.hom.hom.obj ε ⟶ ξ) (hα : 𝒵.val.val.p.IsHomLift k α) :
    k ≫ s = ε.hom ≫ siteMap B S hS (c ≫ π) := by
  let e₁ := schemeStackMapIso B S hS (c ≫ π)
  have hπ : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift k (π.hom.hom.map α) :=
    PresheafOfCategories.isHomLift_map_of_comp π.hom.hom.w k α hα
  have he : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift (𝟙 ε.left)
      (e₁.inv.hom.hom.app ε) := e₁.inv.hom.hom.isHomLift' ε
  have hm : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift (𝟙 ε.left ≫ k)
      (e₁.inv.hom.hom.app ε ≫ π.hom.hom.map α ≫ eqToHom hξ) :=
    @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (𝟙 ε.left) k _ _ he
      (IsHomLift.eqToHom_comp_lift (p := (schemeStack.{u, w} B S hS V).val.val.p) k
        (π.hom.hom.map α) hξ)
  have heq := comp_eq_of_isHomLift_over (a := ε.hom ≫ siteMap B S hS (c ≫ π)) (b := s)
    (𝟙 _ ≫ k) _ hm
  rwa [Category.id_comp] at heq

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The essential image of a 1-morphism of algebraic stacks is inherited along morphisms.**
An object `a` of `𝒴` mapping to an object isomorphic to `f(x)` is isomorphic to `f` of a
restriction of `x`: lift the base morphism to `𝒳`, and fill in over the identity. -/
theorem essImage_of_hom (f : 𝒳 ⟶ 𝒴) {a b : 𝒴.val.val.obj} (φ : a ⟶ b)
    (hb : f.hom.hom.toFunctor.essImage b) : f.hom.hom.toFunctor.essImage a := by
  obtain ⟨x, ⟨e⟩⟩ := hb
  have hfx : 𝒴.val.val.p.obj (f.hom.hom.obj x) = 𝒳.val.val.p.obj x := f.hom.hom.w_obj x
  set m := 𝒴.val.val.p.map (φ ≫ e.inv) ≫ eqToHom hfx
  obtain ⟨x', ψ, hψ⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift m x rfl
  have hfψ : 𝒴.val.val.p.IsHomLift m (f.hom.hom.map ψ) :=
    Functor.isHomLift_map_of_comp_eq f.hom.hom.w m ψ
  have hd : 𝒴.val.val.p.obj a = 𝒴.val.val.p.obj (f.hom.hom.obj x') :=
    (IsHomLift.domain_eq _ m (f.hom.hom.map ψ)).symm
  obtain ⟨χ, ⟨hχ, -⟩, -⟩ := 𝒴.val.isFiberedInGroupoids.unique_lift (f.hom.hom.map ψ)
    (φ ≫ e.inv) (eqToHom hd) (by
      rw [IsHomLift.fac' 𝒴.val.val.p m (f.hom.hom.map ψ)]
      simp [m])
  have : 𝒴.val.val.p.IsHomLift (eqToHom hd) χ := hχ ▸ IsHomLift.map _ χ
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒴.val.isFiberedInGroupoids
    (eqToHom hd) χ
  have : IsIso χ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.val.p (eqToHom hd) χ
  exact ⟨x', ⟨(asIso χ).symm⟩⟩

/-- The **chart image** of a 1-morphism `f : 𝒳 ⟶ 𝒴` along `v : (Sch/V)_fppf ⟶ 𝒴`: the
scheme-theoretic image, in `V`, of the base change `𝒳 ×_𝒴 V ⟶ V`. It is the smallest closed
subspace of `V` containing every `s : T ⟶ V` at which `v(s)` lies in the essential image of `f`,
i.e. which lifts to `𝒳 ×_𝒴 V`. -/
def chartImageSubfunctor (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) : Subfunctor (yoneda.obj V) :=
  Space.schemeTheoreticImageSubfunctor B S hS
    (chartSubfunctor (fun φ hb => essImage_of_hom f φ hb) v).ι

/-- The chart image is a closed subspace. -/
theorem isClosedSubspace_chartImageSubfunctor (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) :
    Space.IsClosedSubspace B S hS (chartImageSubfunctor f v) :=
  Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _ (isAlgebraicSpace_yoneda _ _ _ _)

/-- A morphism `s : T ⟶ V` at which `v(s)` lies in the essential image of `f` lies in the chart
image. -/
theorem mem_chartImageSubfunctor (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) {T : BigFppfOver B S hS} {s : T ⟶ V}
    (hs : f.hom.hom.toFunctor.essImage (v.hom.hom.obj (Over.mk s))) :
    s ∈ (chartImageSubfunctor f v).obj (op T) :=
  Space.range_le_schemeTheoreticImageSubfunctor B S hS _ _ ⟨⟨s, hs⟩, rfl⟩

/-- The chart image is contained in every closed subspace containing the morphisms which lift. -/
theorem chartImageSubfunctor_le (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) {Z : Subfunctor (yoneda.obj V)}
    (hZ : Space.IsClosedSubspace B S hS Z)
    (h : ∀ ⦃T : BigFppfOver B S hS⦄ (s : T ⟶ V),
      f.hom.hom.toFunctor.essImage (v.hom.hom.obj (Over.mk s)) → s ∈ Z.obj (op T)) :
    chartImageSubfunctor f v ≤ Z := by
  refine Space.schemeTheoreticImageSubfunctor_le B S hS _ hZ ?_
  rintro T _ ⟨⟨s, hs⟩, rfl⟩
  exact h s hs

/-- The chart image is unchanged by a 2-isomorphism of charts. -/
theorem chartImageSubfunctor_congr (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    {v v' : schemeStack.{u, w} B S hS V ⟶ 𝒴} (e : v ≅ v') :
    chartImageSubfunctor f v = chartImageSubfunctor f v' := by
  unfold chartImageSubfunctor
  rw [chartSubfunctor_congr _ e]

/-- **The easy half of the flat base change of chart images.** The chart image of
`(Sch/E)_fppf ⟶ (Sch/V)_fppf ⟶ 𝒴` is contained in the inverse image of the chart image of the
second 1-morphism, for any morphism `q : E ⟶ V` of the site. -/
theorem chartImageSubfunctor_comp_le (f : 𝒳 ⟶ 𝒴) {E V : BigFppfOver B S hS} (q : E ⟶ V)
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) :
    chartImageSubfunctor f (schemeStackMap.{u, w} B S hS q ≫ v) ≤
      (chartImageSubfunctor f v).preimage (yoneda.map q) :=
  chartImageSubfunctor_le f _ (Space.isClosedSubspace_preimage B S hS _ _
      (isAlgebraicSpace_yoneda _ _ _ _) (isAlgebraicSpace_yoneda _ _ _ _)
      (isClosedSubspace_chartImageSubfunctor f v))
    fun _ _ hs => mem_chartImageSubfunctor f v hs

/-- **The chart image lies in the scheme-theoretic image of a presentation.** Let
`v : (Sch/V)_fppf ⟶ 𝒴` and let `ρ : (Sch/A)_fppf ⟶ 𝒳 ×_𝒴 V` be smooth and surjective. Then the
chart image of `f` along `v` is contained in the scheme-theoretic image of the morphism
`g : A ⟶ V` of the site underlying `ρ` followed by the projection to `V`: the presentation lifts
the points of `𝒳 ×_𝒴 V` fppf locally (**Stacks 06QA**), and the scheme-theoretic image of `g` is
a sheaf. -/
theorem chartImageSubfunctor_le_schemeTheoreticImageSubfunctor (f : 𝒳 ⟶ 𝒴)
    {V A : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒴)
    (ρ : schemeStack.{u, w} B S hS A ⟶ (twoFibreProductSquareAlgebraicStacks B S hS v f).pt)
    (hρs : IsSurjective B S hS ρ) (hρsm : AlgebraicStacks.IsSmooth B S hS ρ) :
    chartImageSubfunctor f v ≤ Space.schemeTheoreticImageSubfunctor B S hS (yoneda.map
      (siteMap B S hS (ρ ≫ (twoFibreProductSquareAlgebraicStacks B S hS v f).fst))) := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS v f
  set g : A ⟶ V := siteMap B S hS (ρ ≫ P.fst)
  refine chartImageSubfunctor_le f v (Space.isClosedSubspace_schemeTheoreticImageSubfunctor
    B S hS _ (isAlgebraicSpace_yoneda _ _ _ _)) fun T s hs => ?_
  obtain ⟨⟨base, x, y, hx, hy, iso, vert⟩, hξ⟩ :=
    (TwoFibreProductOver.essImage_obj_iff_exists_x_eq v.hom.hom
    f.hom.hom 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids (Over.mk s)).1 hs
  subst hξ
  subst hx
  obtain ⟨R, hR, hlift⟩ := exists_fppfCovering_fibre_lift B S hS ρ hρs
    (AlgebraicStacks.isFlat_of_isSmooth B S hS ρ hρsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS ρ hρsm) T
    ⟨(⟨T, Over.mk s, y, rfl, hy, iso, vert⟩ : TwoFibreProductOver _ _ _ _ _), rfl⟩
  refine Space.mem_obj_of_sieve_le B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS V) _
    (Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _
      (isAlgebraicSpace_yoneda _ _ _ _)).1.isSheaf s R hR fun {T'} k hk => ?_
  obtain ⟨a, α, hα⟩ := hlift hk
  have hT' : a.left = T' :=
    (ρ.hom.hom.w_obj a).symm.trans (IsHomLift.domain_eq P.pt.val.val.p k α)
  subst hT'
  have heq := comp_eq_siteMap_of_isHomLift ρ P.fst rfl a k α hα
  exact Space.range_le_schemeTheoreticImageSubfunctor B S hS _ _ ⟨a.hom, heq.symm⟩

/-- **The hard half of the flat base change of chart images.** Let `f : 𝒳 ⟶ 𝒴` be quasi-compact,
let `v : (Sch/V)_fppf ⟶ 𝒴` with `V` affine, and let `q : E ⟶ V` be a flat morphism of the site.
Then the inverse image along `q` of the chart image of `v` is contained in the chart image of
`(Sch/E)_fppf ⟶ (Sch/V)_fppf ⟶ 𝒴`.

The 2-fibre product `𝒳 ×_𝒴 V` is quasi-compact, `f` being quasi-compact and `V` affine, so it has
a smooth surjective presentation by an affine `A` (**Stacks 04YC**), whose composite to `V` is a
morphism `g : A ⟶ V` of affines, hence quasi-compact. The chart image of `v` is contained in the
scheme-theoretic image of `g`, because the presentation lifts the points of `𝒳 ×_𝒴 V` fppf
locally (**Stacks 06QA**); the scheme-theoretic image of `g` commutes with the flat base change
along `q` (**Stacks 081I**, in the form of **Stacks 089E** for morphisms of the site); and the
base change of `g` along `q` lands in the chart image of the composite. -/
theorem preimage_chartImageSubfunctor_le (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism B S hS f)
    {E V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) (q : E ⟶ V)
    (hq : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    (chartImageSubfunctor f v).preimage (yoneda.map q) ≤
      chartImageSubfunctor f (schemeStackMap.{u, w} B S hS q ≫ v) := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS v f
  have hqc : IsQuasiCompactStack.{u, w} B S hS P.pt.val P.pt.property :=
    hf (schemeStack.{u, w} B S hS V) v
      (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS V inferInstance)
  obtain ⟨A, hA, ρ, hρs, hρsm⟩ := exists_affineAtlas_of_isQuasiCompactStack B S hS P.pt hqc
  set g : A ⟶ V := siteMap B S hS (ρ ≫ P.fst)
  let e₁ : ρ ≫ P.fst ≅ schemeStackMap.{u, w} B S hS g := schemeStackMapIso B S hS (ρ ≫ P.fst)
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  -- the chart image of `v` lies in the scheme-theoretic image of `g`
  have h₁ : chartImageSubfunctor f v ≤
      Space.schemeTheoreticImageSubfunctor B S hS (yoneda.map g) :=
    chartImageSubfunctor_le_schemeTheoreticImageSubfunctor f v ρ hρs hρsm
  -- the scheme-theoretic image of `g` commutes with flat base change along `q`
  have h₂ := Space.schemeTheoreticImageSubfunctor_pullback_snd_yoneda_of_flat B S hS q g
  -- the base change of `g` lands in the chart image of the composite
  have h₃ : Space.schemeTheoreticImageSubfunctor B S hS (yoneda.map (pullback.snd g q)) ≤
      chartImageSubfunctor f (schemeStackMap.{u, w} B S hS q ≫ v) := by
    refine Space.schemeTheoreticImageSubfunctor_le B S hS _
      (isClosedSubspace_chartImageSubfunctor f _) ?_
    rintro T _ ⟨w, rfl⟩
    refine Space.range_le_schemeTheoreticImageSubfunctor B S hS _ _ ⟨⟨_, ?_⟩, rfl⟩
    set a₀ := w ≫ pullback.fst g q
    have hc : (w ≫ pullback.snd g q) ≫ q = a₀ ≫ g := by
      simp [a₀, pullback.condition]
    let ξ := ρ.hom.hom.obj (Over.mk a₀)
    change f.hom.hom.toFunctor.essImage (v.hom.hom.obj (Over.mk ((w ≫ pullback.snd g q) ≫ q)))
    refine essImage_of_hom f (eqToHom (by rw [hc]; rfl) ≫ v.hom.hom.map (e₁.inv.hom.hom.app _))
      ⟨ξ.y, ⟨ξ.iso.symm⟩⟩
  rw [h₂] at h₃
  exact fun T t ht => h₃ T (h₁ T ht)

/-- **A smooth affine chart through every point.** Every point of an algebraic stack is in the
image of a smooth 1-morphism from the algebraic stack of an affine object of the site: restrict a
smooth surjective scheme presentation to an affine open neighbourhood of a preimage. -/
theorem exists_affine_smooth_chart (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (ξ : AlgebraicStacks.points B S hS 𝒴) :
    ∃ (V : BigFppfOver B S hS) (v : schemeStack.{u, w} B S hS V ⟶ 𝒴),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ AlgebraicStacks.IsSmooth B S hS v ∧
        ξ ∈ Set.range (AlgebraicStacks.pointsMap B S hS v) := by
  obtain ⟨U₀, c, hcsm, hcs⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  obtain ⟨η, rfl⟩ := hcs ξ
  have hx : pointsHomeomorphScheme B S hS U₀ η ∈
      (⊤ : ((BigFppfOver.toScheme B S hS).obj U₀).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hx
  obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨V, u, hu, hurange, hVaff⟩ := BigFppfOver.exists_affineOpen_restrict B S hS U₀ O
  obtain ⟨x', hx'⟩ : pointsHomeomorphScheme B S hS U₀ η ∈
      Set.range ((BigFppfOver.toScheme B S hS).map u) := by rw [hurange]; exact hO
  let _ := reprPointTopology B S hS V
  let _ := reprPointTopology B S hS U₀
  refine ⟨V, schemeStackMap.{u, w} B S hS u ≫ c, hVaff, AlgebraicStacks.isSmooth_comp B S hS _ _
    (isSmooth_schemeStackMap.{u, w} B S hS u inferInstance) hcsm,
    (pointsHomeomorphScheme B S hS V).symm x', ?_⟩
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply]
  congr 1
  apply (pointsHomeomorphScheme B S hS U₀).injective
  rw [pointsHomeomorphScheme_pointsMap, siteMap_schemeStackMap, Homeomorph.apply_symm_apply,
    hx']

end ChartImage

section FlatLocalImage

open Opposite

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The flat-local image of a 1-morphism.** The property of an object `y` of `𝒴` that for every
smooth 1-morphism `v : (Sch/V)_fppf ⟶ 𝒴` with `V` affine and every `s : T ⟶ V` with a morphism
`v(s) ⟶ y`, the morphism `s` lies in the chart image of `f` along `v`. Under quasi-compactness of
`f` this cuts out a closed substack of `𝒴` through which `f` factors, whose chart subfunctor along
each such `v` is the chart image: it is the closed substack of `𝒴` that the chart images descend
to, in the proof of **Stacks 0CMK**. -/
def flatLocalImage (f : 𝒳 ⟶ 𝒴) : ObjectProperty 𝒴.val.val.obj := fun y =>
  ∀ ⦃V : BigFppfOver B S hS⦄ (v : schemeStack.{u, w} B S hS V ⟶ 𝒴),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) → AlgebraicStacks.IsSmooth B S hS v →
    ∀ ⦃T : BigFppfOver B S hS⦄ (s : T ⟶ V), Nonempty (v.hom.hom.obj (Over.mk s) ⟶ y) →
      s ∈ (chartImageSubfunctor f v).obj (op T)

/-- The flat-local image is inherited along morphisms. -/
theorem flatLocalImage_of_hom (f : 𝒳 ⟶ 𝒴) {a b : 𝒴.val.val.obj} (φ : a ⟶ b)
    (hb : flatLocalImage f b) : flatLocalImage f a :=
  fun _ v hV hv _ s ⟨β⟩ => hb v hV hv s ⟨β ≫ φ⟩

/-- `f` factors through its flat-local image. -/
theorem flatLocalImage_obj (f : 𝒳 ⟶ 𝒴) (x : 𝒳.val.val.obj) :
    flatLocalImage f (f.hom.hom.obj x) :=
  fun _ v _ _ _ _ ⟨β⟩ => mem_chartImageSubfunctor f v (essImage_of_hom f β ⟨x, ⟨Iso.refl _⟩⟩)

/-- The chart subfunctor of the flat-local image along a smooth affine chart is contained in the
chart image. -/
theorem chartSubfunctor_flatLocalImage_le (f : 𝒳 ⟶ 𝒴) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hv : AlgebraicStacks.IsSmooth B S hS v) :
    chartSubfunctor (fun φ hb => flatLocalImage_of_hom f φ hb) v ≤ chartImageSubfunctor f v :=
  fun _ s hs => hs v hV hv s ⟨𝟙 _⟩

/-- **The flat-local image is local on the big fppf site.** -/
theorem flatLocalImage_of_covering (f : 𝒳 ⟶ 𝒴) ⦃U : BigFppfOver B S hS⦄
    (y : 𝒴.val.val.p.Fiber U) ⦃R : Sieve U⦄ (hR : R ∈ BigFppfOver.topology B S hS U)
    (h : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k →
      k ∈ (objSubfunctor (fun φ hb => flatLocalImage_of_hom f φ hb) y).obj (op V)) :
    flatLocalImage f y.1 := by
  intro V v hV hv T s ⟨β⟩
  have hT : 𝒴.val.val.p.obj (v.hom.hom.obj (Over.mk s)) = T := v.hom.hom.w_obj _
  set g : T ⟶ U := eqToHom hT.symm ≫ 𝒴.val.val.p.map β ≫ eqToHom y.2
  have hg : 𝒴.val.val.p.IsHomLift g β := IsHomLift.of_fac' _ g β hT y.2 (by simp [g])
  refine Space.mem_obj_of_sieve_le B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS V) _
    (isClosedSubspace_chartImageSubfunctor f v).1.isSheaf s (R.pullback g)
    ((BigFppfOver.topology B S hS).pullback_stable g hR) fun {T'} m hm => ?_
  obtain ⟨ζ, α, hα, hζ⟩ := h (m ≫ g) hm
  let n : (Over.mk (m ≫ s) : Over V) ⟶ Over.mk s := Over.homMk m rfl
  have hn : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift m n :=
    (inferInstance : (Over.forget V).IsHomLift ((Over.forget V).map n) n)
  have hvn : 𝒴.val.val.p.IsHomLift m (v.hom.hom.map n) :=
    Functor.isHomLift_map_of_comp_eq v.hom.hom.w m n
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒴.val.isFiberedInGroupoids
    (m ≫ g) α
  exact hζ v hV hv (m ≫ s) ⟨Functor.IsStronglyCartesian.map 𝒴.val.val.p (m ≫ g) α
    (Category.id_comp _).symm (v.hom.hom.map n ≫ β)⟩

/-- **A morphism into a chart restricts to a vertical isomorphism.** A morphism `β : z ⟶ v(s)`
lying over `g` factors through the strongly cartesian arrow `v(g ≫ s) ⟶ v(s)`, by a morphism over
the identity. -/
theorem exists_isHomLift_id_chart {V T₁ T : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) {z : 𝒴.val.val.obj} (g : T₁ ⟶ T) (s : T ⟶ V)
    (β : z ⟶ v.hom.hom.obj (Over.mk s)) (hβ : 𝒴.val.val.p.IsHomLift g β) :
    ∃ χ : z ⟶ v.hom.hom.obj (Over.mk (g ≫ s)), 𝒴.val.val.p.IsHomLift (𝟙 T₁) χ ∧ IsIso χ := by
  let n : (Over.mk (g ≫ s) : Over V) ⟶ Over.mk s := Over.homMk g rfl
  have hn : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift g n :=
    (inferInstance : (Over.forget V).IsHomLift ((Over.forget V).map n) n)
  have hvn : 𝒴.val.val.p.IsHomLift g (v.hom.hom.map n) :=
    Functor.isHomLift_map_of_comp_eq v.hom.hom.w g n
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒴.val.isFiberedInGroupoids g
    (v.hom.hom.map n)
  let χ := Functor.IsStronglyCartesian.map 𝒴.val.val.p g (v.hom.hom.map n)
    (Category.id_comp g).symm β
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒴.val.isFiberedInGroupoids
    (𝟙 T₁) χ
  exact ⟨χ, inferInstance, Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.val.p (𝟙 T₁) χ⟩

/-- The underlying morphism of the site of a flat 1-morphism of represented algebraic stacks is
flat: flatness of the 1-morphism is flatness of the induced morphism of representing algebraic
spaces, i.e. of the morphism of schemes. -/
private theorem flat_siteMap_of_isFlat {E V : BigFppfOver B S hS}
    (m : schemeStack.{u, w} B S hS E ⟶ schemeStack.{u, w} B S hS V)
    (hflat : AlgebraicStacks.IsFlat B S hS m) :
    Flat ((BigFppfOver.toScheme B S hS).map (siteMap B S hS m)) := by
  obtain ⟨q, hq⟩ : ∃ q : E ⟶ V, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS E) (schemeFibredCategory B S hS V)
        (yoneda.obj E) (yoneda.obj V) (representedChart B S hS E)
        (representedChart B S hS V) m.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hq' : Flat ((BigFppfOver.toScheme B S hS).map q) := by
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget q).1 ?_
    rw [hq]
    exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (schemeStack.{u, w} B S hS E).property (schemeStack.{u, w} B S hS V).property
      (yoneda.obj E) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS E) (isAlgebraicSpace_yoneda B S hS V)
      (representedChart B S hS E) (representedChart B S hS V) m.hom).1
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).1 hflat)
  obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (schemeFibredCategory B S hS E) (schemeFibredCategory B S hS V)
    (yoneda.obj E) (yoneda.obj V) (representedChart B S hS E) (representedChart B S hS V)
    (f := m.hom) (g := schemeFibredCategoryMap B S hS q)
    (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
  have hqq : siteMap B S hS m = q :=
    (siteMap_eq_of_iso B S hS (Bicategory.InducedBicategory.isoMk hu.default :
      m ≅ schemeStackMap.{u, w} B S hS q)).trans (siteMap_schemeStackMap.{u, w} B S hS q)
  rwa [hqq]

/-- **The chart images of smooth affine charts are invariant (the claim of the proof of Stacks
0CMK).** For `f` quasi-compact and `v` a smooth chart by an affine `V`, the chart image of `v` is
contained in the chart subfunctor of the flat-local image.

Given `s` in the chart image of `v` and a morphism `v₁(s₁) ⟶ v(s)` from another smooth affine
chart, the point `(s₁, s)` of `(Sch/V₁) ×_𝒴 (Sch/V)` lifts fppf locally to a smooth scheme
presentation `E` of that 2-fibre product; the projection `E ⟶ V` is smooth, so flat base change
(`AlgebraicGeometry.Stack.preimage_chartImageSubfunctor_le`) carries the chart image of `v` into
the chart image of `E ⟶ 𝒴`, which maps into the chart image of `v₁` along `E ⟶ V₁`. -/
theorem chartImageSubfunctor_le_chartSubfunctor_flatLocalImage (f : 𝒳 ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism B S hS f) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒴) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    chartImageSubfunctor f v ≤ chartSubfunctor (fun φ hb => flatLocalImage_of_hom f φ hb) v := by
  rintro ⟨T⟩ s hs
  change flatLocalImage f (v.hom.hom.obj (Over.mk s))
  intro V₁ v₁ hV₁ hv₁ T₁ s₁ ⟨β⟩
  have hT₁ : 𝒴.val.val.p.obj (v₁.hom.hom.obj (Over.mk s₁)) = T₁ := v₁.hom.hom.w_obj _
  have hT : 𝒴.val.val.p.obj (v.hom.hom.obj (Over.mk s)) = T := v.hom.hom.w_obj _
  set g : T₁ ⟶ T := eqToHom hT₁.symm ≫ 𝒴.val.val.p.map β ≫ eqToHom hT
  have hg : 𝒴.val.val.p.IsHomLift g β := IsHomLift.of_fac' _ g β hT₁ hT (by simp [g])
  obtain ⟨χ, hχ, _⟩ := exists_isHomLift_id_chart v g s β hg
  let sq₂ := twoFibreProductSquareAlgebraicStacks B S hS v₁ v
  have hsq₂ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS v₁ v
  have hsnd : AlgebraicStacks.IsSmooth B S hS sq₂.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS v₁ v sq₂.swap
      (Bicategory.isTwoFibreProduct_swap hsq₂) hv₁
  obtain ⟨E, c, hcsm, hcs⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS sq₂.pt
  set q₀ := siteMap B S hS (c ≫ sq₂.snd)
  set q₁ := siteMap B S hS (c ≫ sq₂.fst)
  have hq₀ : Flat ((BigFppfOver.toScheme B S hS).map q₀) :=
    flat_siteMap_of_isFlat _ (AlgebraicStacks.isFlat_of_isSmooth B S hS _
      (AlgebraicStacks.isSmooth_comp B S hS c sq₂.snd hcsm hsnd))
  let e : schemeStackMap.{u, w} B S hS q₀ ≫ v ≅ schemeStackMap.{u, w} B S hS q₁ ≫ v₁ :=
    Bicategory.whiskerRightIso (schemeStackMapIso B S hS (c ≫ sq₂.snd)).symm v ≪≫
      Bicategory.associator c sq₂.snd v ≪≫ Bicategory.whiskerLeftIso c sq₂.iso.symm ≪≫
      (Bicategory.associator c sq₂.fst v₁).symm ≪≫
      Bicategory.whiskerRightIso (schemeStackMapIso B S hS (c ≫ sq₂.fst)) v₁
  let ξ : sq₂.pt.val.val.obj :=
    (⟨T₁, Over.mk s₁, Over.mk (g ≫ s), rfl, rfl, asIso χ, hχ⟩ : TwoFibreProductOver _ _ _ _ _)
  obtain ⟨R, hR, hlift⟩ := exists_fppfCovering_fibre_lift B S hS c hcs
    (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) T₁ ⟨ξ, rfl⟩
  refine Space.mem_obj_of_sieve_le B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS V₁) _
    (isClosedSubspace_chartImageSubfunctor f v₁).1.isSheaf s₁ R hR fun {T'} k hk => ?_
  obtain ⟨ε, α, hα⟩ := hlift hk
  have hT' : ε.left = T' :=
    (c.hom.hom.w_obj ε).symm.trans (IsHomLift.domain_eq sq₂.pt.val.val.p k α)
  subst hT'
  have e₀ := comp_eq_siteMap_of_isHomLift c sq₂.snd (s := g ≫ s) (ξ := ξ) rfl ε k α hα
  have e₁ := comp_eq_siteMap_of_isHomLift c sq₂.fst (s := s₁) (ξ := ξ) rfl ε k α hα
  have h₀ : ε.hom ∈ ((chartImageSubfunctor f v).preimage (yoneda.map q₀)).obj (op ε.left) := by
    change ε.hom ≫ q₀ ∈ (chartImageSubfunctor f v).obj (op ε.left)
    rw [← e₀, ← Category.assoc]
    exact (chartImageSubfunctor f v).map (k ≫ g).op hs
  have h₁ := preimage_chartImageSubfunctor_le f hf hV v q₀ hq₀ _ h₀
  rw [chartImageSubfunctor_congr f e] at h₁
  have h₂ := chartImageSubfunctor_comp_le f q₁ v₁ _ h₁
  change k ≫ s₁ ∈ (chartImageSubfunctor f v₁).obj (op ε.left)
  rwa [e₁]

/-- Along a smooth chart by an affine object, the chart subfunctor of the flat-local image of a
quasi-compact `f` is the chart image of `f`. -/
theorem chartSubfunctor_flatLocalImage (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism B S hS f)
    {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒴)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (hv : AlgebraicStacks.IsSmooth B S hS v) :
    chartSubfunctor (fun φ hb => flatLocalImage_of_hom f φ hb) v = chartImageSubfunctor f v :=
  le_antisymm (chartSubfunctor_flatLocalImage_le f v hV hv)
    (chartImageSubfunctor_le_chartSubfunctor_flatLocalImage f hf v hV)

/-- **The flat-local image of a quasi-compact 1-morphism is a closed substack.** Its chart
subfunctors along the smooth affine charts are the chart images, which are closed subspaces, and
those charts cover `𝒴`; this is the descent of **Stacks 0507** in the form
`AlgebraicGeometry.Stack.isClosedSubstack_of_isClosedSubspace_chartSubfunctor`. -/
theorem isClosedSubstack_flatLocalImage (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism B S hS f) :
    IsClosedSubstack 𝒴 (flatLocalImage f) := by
  let J := Σ V : BigFppfOver B S hS, {v : schemeStack.{u, w} B S hS V ⟶ 𝒴 //
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ AlgebraicStacks.IsSmooth B S hS v}
  refine isClosedSubstack_of_isClosedSubspace_chartSubfunctor
    (fun φ hb => flatLocalImage_of_hom f φ hb) (flatLocalImage_of_covering f)
    (V := fun j : J => j.1) (fun j => j.2.1) (fun j => j.2.2.2) ?_ fun j => ?_
  · refine (Set.eq_univ_of_forall fun ξ => ?_).symm
    obtain ⟨V, v, hV, hv, hξ⟩ := exists_affine_smooth_chart 𝒴 ξ
    exact Set.mem_iUnion.2 ⟨⟨V, v, hV, hv⟩, hξ⟩
  · rw [chartSubfunctor_flatLocalImage f hf j.2.1 j.2.2.1 j.2.2.2]
    exact isClosedSubspace_chartImageSubfunctor f _

/-- `f` factors through its flat-local image. -/
theorem factorsThroughSubstack_flatLocalImage (f : 𝒳 ⟶ 𝒴) :
    FactorsThroughSubstack f (flatLocalImage f) := by
  have : (flatLocalImage f).IsClosedUnderIsomorphisms :=
    ⟨fun e hb => flatLocalImage_of_hom f e.inv hb⟩
  exact (factorsThroughSubstack_iff_forall f).2 (flatLocalImage_obj f)

end FlatLocalImage

section Main

open Opposite

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **The inverse image of the flat-local image under a flat 1-morphism lies in the scheme
theoretic image of the base change.** Let `f` be quasi-compact and `b : 𝒴' ⟶ 𝒴` flat, and let
`f' : 𝒳 ×_𝒴 𝒴' ⟶ 𝒴'` be the base change. Every object `y'` of `𝒴'` whose image under `b` lies
in the flat-local image of `f` lies in the scheme theoretic image of `f'`.

`𝒴'` is covered by smooth charts `E ⟶ 𝒴' ×_𝒴 V ⟶ 𝒴'` over the smooth affine charts `V` of `𝒴`,
whose projections `E ⟶ V` are flat, `b` being flat. Along such a chart the flat-local image is the
inverse image of the chart image of `V`, which is contained in the chart image of `E ⟶ 𝒴` by flat
base change (`AlgebraicGeometry.Stack.preimage_chartImageSubfunctor_le`), and the chart image of
`E ⟶ 𝒴' ⟶ 𝒴` lies in the chart subfunctor of the scheme theoretic image of `f'`, a closed
subspace (Stacks 0507) containing everything that lifts to `𝒳 ×_𝒴 𝒴'`. Membership of a closed
substack is local, so `y'` lies in it. -/
theorem inverseImage_flatLocalImage_le (f : 𝒳 ⟶ 𝒴) (b : 𝒴' ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism B S hS f) (hb : AlgebraicStacks.IsFlat B S hS b) :
    (flatLocalImage f).inverseImage b.hom.hom.toFunctor ≤
      schemeTheoreticImageCandidate (twoFibreProductSquareAlgebraicStacks B S hS b f).fst := by
  set sq := twoFibreProductSquareAlgebraicStacks B S hS b f
  set P' := schemeTheoreticImageCandidate sq.fst
  have hP'c : IsClosedSubstack 𝒴' P' := isClosedSubstack_schemeTheoreticImageCandidate sq.fst
  have hP'i : ∀ {a c : 𝒴'.val.val.obj}, (a ⟶ c) → P' c → P' a := fun φ hc => hP'c.prop_of_hom φ hc
  -- the charts of `𝒴'`, indexed by the smooth affine charts of `𝒴`
  let J := Σ V : BigFppfOver B S hS, {v : schemeStack.{u, w} B S hS V ⟶ 𝒴 //
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ AlgebraicStacks.IsSmooth B S hS v}
  let sqJ : ∀ j : J, Bicategory.TwoCommSq j.2.1 b := fun j =>
    twoFibreProductSquareAlgebraicStacks B S hS j.2.1 b
  have hsqJ : ∀ j : J, Bicategory.IsTwoFibreProduct (sqJ j) := fun j =>
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS j.2.1 b
  choose E c hcsm hcs using fun j : J =>
    exists_smooth_surjective_schemeStack.{u, w} B S hS (sqJ j).pt
  let u : ∀ j : J, schemeStack.{u, w} B S hS (E j) ⟶ 𝒴' := fun j => c j ≫ (sqJ j).snd
  have hu : ∀ j, AlgebraicStacks.IsSmooth B S hS (u j) := fun j =>
    AlgebraicStacks.isSmooth_comp B S hS _ _ (hcsm j)
      (AlgebraicStacks.isSmooth_baseChange B S hS j.2.1 b (sqJ j).swap
        (Bicategory.isTwoFibreProduct_swap (hsqJ j)) j.2.2.2)
  have hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴')) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (u j)) := by
    refine (Set.eq_univ_of_forall fun ξ => ?_).symm
    obtain ⟨V, v, hV, hv, z, hz⟩ :=
      exists_affine_smooth_chart 𝒴 (AlgebraicStacks.pointsMap B S hS b ξ)
    let j : J := ⟨V, v, hV, hv⟩
    obtain ⟨p, -, hp⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS (sqJ j) (hsqJ j)
      z ξ hz
    obtain ⟨t, rfl⟩ := hcs j p
    refine Set.mem_iUnion.2 ⟨j, t, ?_⟩
    change AlgebraicStacks.pointsMap B S hS (c j ≫ (sqJ j).snd) t = _
    rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply]
    exact hp
  -- along each chart, the flat-local image lies in the scheme theoretic image of `f'`
  have key : ∀ (j : J) (ε : Over (E j)), flatLocalImage f (b.hom.hom.obj ((u j).hom.hom.obj ε)) →
      P' ((u j).hom.hom.obj ε) := by
    intro j ε hε
    set q := siteMap B S hS (c j ≫ (sqJ j).fst)
    have hq : Flat ((BigFppfOver.toScheme B S hS).map q) :=
      flat_siteMap_of_isFlat _ (AlgebraicStacks.isFlat_comp B S hS _ _
        (AlgebraicStacks.isFlat_of_isSmooth B S hS _ (hcsm j))
        (AlgebraicStacks.isFlat_baseChange B S hS b j.2.1 (sqJ j) (hsqJ j) hb))
    let e : schemeStackMap.{u, w} B S hS q ≫ j.2.1 ≅ u j ≫ b :=
      Bicategory.whiskerRightIso (schemeStackMapIso B S hS (c j ≫ (sqJ j).fst)).symm j.2.1 ≪≫
        Bicategory.associator (c j) (sqJ j).fst j.2.1 ≪≫ Bicategory.whiskerLeftIso (c j) (sqJ j).iso
        ≪≫ (Bicategory.associator (c j) (sqJ j).snd b).symm
    have h₁ : ε.hom ∈ ((chartImageSubfunctor f j.2.1).preimage (yoneda.map q)).obj
        (op ε.left) :=
      hε j.2.1 j.2.2.1 j.2.2.2 (ε.hom ≫ q)
        ⟨(CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS e)).hom.app
          (Over.mk ε.hom)⟩
    have h₂ := preimage_chartImageSubfunctor_le f hf j.2.2.1 j.2.1 q hq _ h₁
    rw [chartImageSubfunctor_congr f e] at h₂
    have h₃ : chartImageSubfunctor f (u j ≫ b) ≤ chartSubfunctor hP'i (u j) := by
      refine chartImageSubfunctor_le f _ (isClosedSubspace_chartSubfunctor hP'i hP'c (u j))
        fun T s hs => ?_
      obtain ⟨ζ, hζ⟩ := (TwoFibreProductOver.essImage_obj_iff_exists_x_eq b.hom.hom f.hom.hom
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids _).1 hs
      have : P'.IsClosedUnderIsomorphisms := hP'c.1
      have hP := (factorsThroughSubstack_iff_forall sq.fst).1
        (factorsThroughSubstack_schemeTheoreticImageCandidate sq.fst) ζ
      change P' ζ.x at hP
      rwa [hζ] at hP
    exact h₃ _ h₂
  intro y' hy'
  have hcl := isClosedSubspace_objSubfunctor hP'i hP'c (⟨y', rfl⟩ : 𝒴'.val.val.p.Fiber _)
  obtain ⟨I, W, e, a, het, hsurj, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS u hu hjs _ (⟨y', rfl⟩ : 𝒴'.val.val.p.Fiber _)
  have hR := mem_topology_of_family B S hS W e (fun i => by have := het i; infer_instance)
    (fun i => by have := het i; infer_instance) hsurj
  rw [← id_mem_objSubfunctor_iff hP'i ⟨y', rfl⟩]
  refine Space.mem_obj_of_sieve_le B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS _) _
    hcl.1.isSheaf _ _ hR ?_
  rintro T k ⟨_, g, _, ⟨i⟩, rfl⟩
  obtain ⟨x, α, hα⟩ := hlift i
  change (g ≫ _) ≫ 𝟙 _ ∈ _
  rw [Category.comp_id]
  refine (objSubfunctor hP'i ⟨y', rfl⟩).map g.op ?_
  rw [mem_objSubfunctor_iff hP'i _ _ α]
  exact key (a i) x (flatLocalImage_of_hom f (b.hom.hom.map α) hy')

/-- **Stacks 0CMK.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S`
and let `b : 𝒴' ⟶ 𝒴` be a flat 1-morphism. Then formation of the scheme theoretic image commutes
with the base change along `b`: if `P` is the scheme theoretic image of `f`, then its inverse
image under `b` is the scheme theoretic image of the base change
`f' : 𝒳 ×_𝒴 𝒴' ⟶ 𝒴'` (the first projection of the canonical 2-fibre product square).

The containment of the image of `f'` in the inverse image of `P` holds for any square
(`AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_le_inverseImage`). For the converse, the
flat-local image of `f` — the closed substack of `𝒴` cut out by the scheme theoretic images of
the base changes of `f` to the smooth affine charts of `𝒴`, which descend by the invariance of
the proof of Stacks 0CMK
(`AlgebraicGeometry.Stack.chartImageSubfunctor_le_chartSubfunctor_flatLocalImage`) — is a closed
substack through which `f` factors, so it contains `P`, and its inverse image under `b` lies in
the image of `f'` (`AlgebraicGeometry.Stack.inverseImage_flatLocalImage_le`). -/
@[stacks 0CMK, ega "IV 2.3.2" "more general"]
theorem isSchemeTheoreticImage_inverseImage_of_isFlat (f : 𝒳 ⟶ 𝒴) (b : 𝒴' ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism B S hS f) (hb : AlgebraicStacks.IsFlat B S hS b)
    {P : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    IsSchemeTheoreticImage (twoFibreProductSquareAlgebraicStacks B S hS b f).fst
      (P.inverseImage b.hom.hom.toFunctor) := by
  set sq := twoFibreProductSquareAlgebraicStacks B S hS b f
  have heq : P.inverseImage b.hom.hom.toFunctor = schemeTheoreticImageCandidate sq.fst := by
    refine le_antisymm ?_ ?_
    · have hPQ : P ≤ flatLocalImage f :=
        hP.2.2 _ (isClosedSubstack_flatLocalImage f hf) (factorsThroughSubstack_flatLocalImage f)
      exact fun y hy => inverseImage_flatLocalImage_le f b hf hb y (hPQ _ hy)
    · rw [eq_schemeTheoreticImageCandidate hP]
      exact schemeTheoreticImageCandidate_le_inverseImage f b sq
  exact heq ▸ isSchemeTheoreticImage_schemeTheoreticImageCandidate sq.fst

/-- **Stacks 0CMK** for the candidate images: for `f` quasi-compact and `b` flat, the intersection
of the closed substacks of `𝒴'` through which the base change of `f` factors is the inverse image
of the intersection of the closed substacks of `𝒴` through which `f` factors. -/
theorem schemeTheoreticImageCandidate_twoFibreProduct_fst (f : 𝒳 ⟶ 𝒴) (b : 𝒴' ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism B S hS f) (hb : AlgebraicStacks.IsFlat B S hS b) :
    schemeTheoreticImageCandidate (twoFibreProductSquareAlgebraicStacks B S hS b f).fst =
      (schemeTheoreticImageCandidate f).inverseImage b.hom.hom.toFunctor :=
  (eq_schemeTheoreticImageCandidate (isSchemeTheoreticImage_inverseImage_of_isFlat f b hf hb
    (isSchemeTheoreticImage_schemeTheoreticImageCandidate f))).symm

end Main

end AlgebraicGeometry.Stack

end
