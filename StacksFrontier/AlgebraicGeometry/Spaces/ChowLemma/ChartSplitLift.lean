module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSeparableSections
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartPointDistinctLift

/-!
# A field-valued point of the minimal-degree locus lifts to the complement of the diagonals

This file closes the one scheme-to-site translation which the surjectivity step of
[Stacks, Tag 089J] needs. On the one side,
`Stacks.Morphisms.exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank` produces `d`
pairwise distinct morphisms of *schemes* `Spec K' ⟶ Z` over `Spec K`, where `Z` is the fibre of
the chart at a `K`-valued point of the algebraic space and `K'/K` is a finite separable
extension. On the other side,
`AlgebraicGeometry.Space.SpacesEtale.exists_comp_diagonalComplementProj_eq` consumes `d`
pairwise distinct morphisms *of the site* out of one field spectrum, lying over one point of the
algebraic space. The two do not meet: the first lands in the fibre and in the category of
schemes, the second starts from the site and lands in the chart.

The translation has three parts. The extension `K'` is placed in the site because it is finite
over `K`, so `Spec K'` has no larger size than `Spec K` by Stacks 04T7. The morphisms
`Spec K' ⟶ Z` are lifted to morphisms of the site through fullness of the site's inclusion into
schemes, their triangles over the base being those of the fibre. And distinctness survives the
passage from the fibre to the chart — which is *not* a monomorphism — because the fibre is a
fibre product: two morphisms into it which agree over the chart and over `Spec K` agree.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.contains_spec_of_module_finite`: a finite extension of a field whose
  spectrum lies in the site has its spectrum in the site too.
* `AlgebraicGeometry.Space.exists_injective_hom_of_isFiniteLocallyFreeOfRank_fibre`: **the
  scheme-to-site translation.** If the fibre of an étale chart at a `K`-valued point of the
  algebraic space is finite locally free of rank `d`, then after a finite separable extension
  `K'/K` inside the site there are `d` pairwise distinct morphisms of the site
  `Spec K' ⟶ W` into the chart, all lying over the induced `K'`-valued point.
* `AlgebraicGeometry.Space.SpacesEtale.exists_hom_diagonalComplement_of_fibre`: those `d`
  morphisms assemble into a `K'`-point of the complement of the diagonals in the `d`-fold
  self-product of the chart whose projections are exactly them.
* `AlgebraicGeometry.Space.SpacesEtale.mem_range_pointsMap_diagonalComplementProj_comp`: **the
  covering half of the surjectivity step of [Stacks, Tag 089J]**: a point of the algebraic space
  at which the chart has fibre degree `d` lies in the image of the `i`-th projection of the
  complement of the diagonals in the `d`-fold self-product followed by the chart.

## Implementation notes

The rank hypothesis is taken on an arbitrary representable presentation `(Vf, q, iW)` of the
fibre rather than on the canonical one of
`CategoryTheory.Functor.relativelyRepresentable.pullback`, because the consumer — the
stratification of
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'` — delivers the
rank for a presentation it chooses itself. Étaleness of the fibre is *not* a hypothesis: it is
read off the chart through `CategoryTheory.MorphismProperty.relative.property` applied to the
given presentation.

The underlying scheme of the site object of a field-valued point is the spectrum of that field
definitionally, so no comparison isomorphism appears; `Spec K` and
`(BigFppfOver.toScheme B S hS).obj (AlgebraicGeometry.siteObject B S hS hK b)` are
interchangeable throughout.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute. The splitting of the fibre after a separable extension is Stacks 00U3 and 02KA,
carried by `Stacks.Morphisms.exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank`; the
size estimate is Stacks 04T7, carried by
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`; the passage from distinct chart
points to a point of the complement of the diagonals is
`AlgebraicGeometry.Space.SpacesEtale.exists_comp_diagonalComplementProj_eq`.

Nothing here identifies the locus on which the fibre degree equals `d`: the degree hypothesis is
taken at a single field-valued point and the conclusion is about that point only. Nor is
properness or H-quasi-projectivity of the cover of [Stacks, Tag 089J] touched.

## References

* [Stacks Project, Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A finite extension stays inside the site -/

/-- **A finite extension of a field whose spectrum lies in the chosen big fppf site has its
spectrum in the site too.** The structure morphism `Spec K' ⟶ Spec K` is of finite type because
`K'` is a finite `K`-module, and the source of a morphism locally of finite type with compact
source has size at most that of the target by Stacks 04T7. -/
theorem contains_spec_of_module_finite {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [Module.Finite K K'] (hK : B.Contains (Spec (CommRingCat.of K))) :
    B.Contains (Spec (CommRingCat.of K')) := by
  have hlft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 (Module.Finite.finiteType (R := K) (A := K'))
  have _ := hlft
  exact lt_of_le_of_lt
    (Scheme.size_le_of_locallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))) hK

/-! ### The scheme-to-site translation -/

/-- **A field-valued point whose chart fibre is finite locally free of rank `d` acquires `d`
pairwise distinct lifts to the chart, as morphisms of the site, after a finite separable
extension of the field.**

The data is a chart `c : h_W ⟶ X` which is étale, a `K`-valued point `ξ` of `X` for a field `K`
in the site, and a representable presentation `(Vf, q, iW)` of the fibre of `c` at `ξ` whose
projection `q` to the point is finite locally free of rank `d`.

The fibre is étale over `Spec K` because the chart is étale, so
`Stacks.Morphisms.exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank` splits it
completely over a finite separable extension `K'/K`: there are `d` pairwise distinct morphisms
of schemes `Spec K' ⟶ Vf` over `Spec K`. That extension lies in the site by
`AlgebraicGeometry.Space.contains_spec_of_module_finite`, and the morphisms lift to the site
because its inclusion into schemes is full; composing with the projection to the chart gives the
`d` morphisms claimed.

Distinctness is preserved although the projection `Vf ⟶ W` need not be a monomorphism: two
morphisms of the site into `Vf` which agree after `iW` and after `q` are equal, because
`yoneda.obj Vf` is a fibre product of `c` and `ξ`, and the `d` morphisms all have the same
composite with `q`. -/
theorem exists_injective_hom_of_isFiniteLocallyFreeOfRank_fibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    (hc : IsEtale B S hS c) (d : ℕ) {K : Type u} [Field K]
    (hK : B.Contains (Spec (CommRingCat.of K))) (b : Spec (CommRingCat.of K) ⟶ S)
    (ξ : yoneda.obj (siteObject B S hS hK b) ⟶ X)
    (Vf : BigFppfOver B S hS) (q : Vf ⟶ siteObject B S hS hK b) (iW : Vf ⟶ W)
    (hsq : IsPullback (yoneda.map iW) (yoneda.map q) c ξ)
    (hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q) d) :
    ∃ (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (CommRingCat.of K')))
      (b' : Spec (CommRingCat.of K') ⟶ S)
      (ε : siteObject B S hS hK' b' ⟶ siteObject B S hS hK b)
      (w : Fin d → (siteObject B S hS hK' b' ⟶ W)),
      Function.Injective w ∧ ∀ k, yoneda.map (w k) ≫ c = yoneda.map ε ≫ ξ := by
  classical
  -- the fibre is étale over the spectrum of `K`, because the chart is étale
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    ((isEtale_iff_presheaf_of_yoneda B S hS c).1 hc).property ξ (yoneda.map iW) q hsq
  obtain ⟨K', instK', instAlg, instFin, instSep, σ, hσinj, hσ⟩ :=
    Stacks.Morphisms.exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q) d hrank hetale
  have hK' : B.Contains (Spec (CommRingCat.of K')) :=
    contains_spec_of_module_finite B (K := K) (K' := K') hK
  set φ : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K')) with hφ
  set b' : Spec (CommRingCat.of K') ⟶ S := φ ≫ b with hb'
  -- the structure morphism of the fibre, read in schemes
  have hVfhom : (BigFppfOver.toScheme B S hS).map q ≫ b = B.inclusion.map Vf.hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w q))
  -- the extension, as a morphism of the site
  let ε : siteObject B S hS hK' b' ⟶ siteObject B S hS hK b :=
    Over.homMk (ObjectProperty.homMk φ) rfl
  have hεmap : (BigFppfOver.toScheme B S hS).map ε = φ := rfl
  -- the `d` morphisms of the site into the fibre
  have hσbase : ∀ k, σ k ≫ B.inclusion.map Vf.hom = b' := fun k ↦ by
    rw [← hVfhom, ← Category.assoc, hσ k, hb']
  let s : Fin d → (siteObject B S hS hK' b' ⟶ Vf) := fun k ↦
    Over.homMk (B.inclusion.preimage (X := B.obj hK') (Y := Vf.left)
        (show B.inclusion.obj (B.obj hK') ⟶ B.inclusion.obj Vf.left from σ k))
      (B.inclusion.map_injective <| by
        rw [Functor.map_comp, B.inclusion.map_preimage]
        exact hσbase k)
  have hsmap : ∀ k, (BigFppfOver.toScheme B S hS).map (s k) =
      (show (BigFppfOver.toScheme B S hS).obj (siteObject B S hS hK' b') ⟶
        (BigFppfOver.toScheme B S hS).obj Vf from σ k) :=
    fun k ↦ B.inclusion.map_preimage _
  -- each of them lies over the extension
  have hsq' : ∀ k, s k ≫ q = ε := fun k ↦ (BigFppfOver.toScheme B S hS).map_injective <| by
    rw [Functor.map_comp, hsmap k, hεmap]
    exact hσ k
  refine ⟨K', instK', hK', b', ε, fun k ↦ s k ≫ iW, ?_, ?_⟩
  · intro k l hkl
    have h1 : yoneda.map (s k) ≫ yoneda.map iW = yoneda.map (s l) ≫ yoneda.map iW := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map hkl
    have h2 : yoneda.map (s k) ≫ yoneda.map q = yoneda.map (s l) ≫ yoneda.map q := by
      rw [← Functor.map_comp, ← Functor.map_comp, hsq' k, hsq' l]
    have h3 : yoneda.map (s k) = yoneda.map (s l) := hsq.hom_ext h1 h2
    exact hσinj (((hsmap k).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (yoneda.map_injective h3))).trans (hsmap l))
  · intro k
    rw [Functor.map_comp, Category.assoc, hsq.w, ← Category.assoc, ← Functor.map_comp,
      hsq' k]

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-! ### The lift to the complement of the diagonals -/

/-- **A field-valued point whose chart fibre is finite locally free of rank `m + 1` lifts to the
complement of the diagonals in the `(m + 1)`-fold self-product of the chart.**

This is
`AlgebraicGeometry.Space.exists_injective_hom_of_isFiniteLocallyFreeOfRank_fibre` followed by
`AlgebraicGeometry.Space.SpacesEtale.exists_comp_diagonalComplementProj_eq`: the first produces
`m + 1` pairwise distinct morphisms of the site into the chart over one point of the algebraic
space, after a finite separable extension of the field, and the second assembles them into a
point of the complement of the diagonals whose projections are exactly them.

The conclusion is recorded as the composite with the chart, which is the form in which the
surjectivity step of [Stacks, Tag 089J] uses it: the lift lies over the given point of the
algebraic space, read along the extension `ε`. -/
theorem exists_hom_diagonalComplement_of_fibre
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (m : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).obj)
    {K : Type u} [Field K] (hK : B.Contains (Spec (CommRingCat.of K)))
    (b : Spec (CommRingCat.of K) ⟶ S)
    (ξ : yoneda.obj (siteObject B S hS hK b) ⟶ X.obj)
    (Vf : BigFppfOver B S hS) (q : Vf ⟶ siteObject B S hS hK b) (iW : Vf ⟶ W)
    (hsq : IsPullback (yoneda.map iW) (yoneda.map q) c ξ)
    (hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q) (m + 1)) :
    ∃ (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (CommRingCat.of K')))
      (b' : Spec (CommRingCat.of K') ⟶ S)
      (ε : siteObject B S hS hK' b' ⟶ siteObject B S hS hK b)
      (t₀ : siteObject B S hS hK' b' ⟶ V),
      ∀ k, yoneda.map (t₀ ≫ diagonalComplementProj B S hS X W c hc hsep (m + 1) V e k) ≫ c =
        yoneda.map ε ≫ ξ := by
  obtain ⟨K', instK', hK', b', ε, w, hwinj, hwover⟩ :=
    exists_injective_hom_of_isFiniteLocallyFreeOfRank_fibre B S hS W c hc (m + 1) hK b ξ
      Vf q iW hsq hrank
  obtain ⟨t₀, ht₀⟩ :=
    exists_comp_diagonalComplementProj_eq B S hS X W c hc hsep m V e hK' b' w hwinj
      (fun k ↦ (hwover k).trans (hwover 0).symm)
  exact ⟨K', instK', hK', b', ε, t₀, fun k ↦ by rw [ht₀ k]; exact hwover k⟩

/-- **The covering half of the surjectivity step of [Stacks, Tag 089J].** A point of the
algebraic space at which the fibre of the chart is finite locally free of rank `m + 1` lies in
the image, on points, of the `i`-th projection of the complement of the diagonals in the
`(m + 1)`-fold self-product of the chart followed by the chart.

This is the statement which the source proves over the open where the fibre degree of the chart
is minimal, and which, through
`AlgebraicGeometry.Space.isSurjective_of_isSurjective_comp` and
`AlgebraicGeometry.Space.yoneda_map_chowDenseIncl_comp`, makes the image of the cover of
[Stacks, Tag 089J] contain that open.

The lift of `AlgebraicGeometry.Space.SpacesEtale.exists_hom_diagonalComplement_of_fibre` is
defined over a field extension `K'/K`, so the point it names is a priori a point of
`Spec K'`; it has the given point as its image because the point set of the spectrum of a field,
read as a representable presheaf, is a singleton, so the extension `ε` carries the canonical
point of `Spec K'` to the canonical point of `Spec K`. -/
theorem mem_range_pointsMap_diagonalComplementProj_comp
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (m : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).obj)
    {K : Type u} [Field K] (hK : B.Contains (Spec (CommRingCat.of K)))
    (b : Spec (CommRingCat.of K) ⟶ S)
    (ξ : yoneda.obj (siteObject B S hS hK b) ⟶ X.obj)
    (Vf : BigFppfOver B S hS) (q : Vf ⟶ siteObject B S hS hK b) (iW : Vf ⟶ W)
    (hsq : IsPullback (yoneda.map iW) (yoneda.map q) c ξ)
    (hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map q) (m + 1))
    (i : Fin (m + 1)) :
    pointsMap B S hS _ ξ (fieldSpecPoint B S hS hK b) ∈
      Set.range (pointsMap B S hS (yoneda.obj V)
        (yoneda.map (diagonalComplementProj B S hS X W c hc hsep (m + 1) V e i) ≫ c)) := by
  obtain ⟨K', instK', hK', b', ε, t₀, ht₀⟩ :=
    exists_hom_diagonalComplement_of_fibre B S hS X W c hc hsep m V e hK b ξ Vf q iW hsq hrank
  have hsub : Subsingleton (points B S hS (yoneda.obj (siteObject B S hS hK b))) :=
    subsingleton_points_yoneda_siteObject B S hS
      ({ carrier := K, contained := hK, toBase := b, value := 𝟙 _ } :
        FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS hK b)))
  refine ⟨pointsMap B S hS (yoneda.obj (siteObject B S hS hK' b')) (yoneda.map t₀)
    (fieldSpecPoint B S hS hK' b'), ?_⟩
  rw [← pointsMap_comp_apply, ← Category.assoc, ← Functor.map_comp, ht₀ i, pointsMap_comp_apply,
    hsub.elim (pointsMap B S hS (yoneda.obj (siteObject B S hS hK' b')) (yoneda.map ε)
      (fieldSpecPoint B S hS hK' b')) (fieldSpecPoint B S hS hK b)]

end SpacesEtale

end AlgebraicGeometry.Space

end
