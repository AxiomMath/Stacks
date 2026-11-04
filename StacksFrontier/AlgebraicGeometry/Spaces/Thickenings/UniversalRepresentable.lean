module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal

/-!
# A universal first-order thickening of schemes is one of the algebraic spaces they represent

Let `i : V ⟶ V'` and `p : V' ⟶ U` be morphisms of the big fppf category over a scheme `S`, and
suppose the underlying closed immersion of schemes `V ⟶ V'` is a universal first-order
thickening of `V` over `U` in the sense of `Stacks.Thickenings.IsUniversalFirstOrderThickening`.
Then the range of `yoneda.map i` is a universal first-order thickening of the algebraic space
represented by `V` over the algebraic space represented by `U`, in the sense of
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening`.

The two universal properties are not the same statement. The scheme-level one tests the
diagrams of Stacks 0602 whose ambient object is a *scheme*; the space-level one tests those
whose ambient object is an arbitrary *algebraic space* over `S`, so it is formally the stronger
of the two. The passage from one to the other is Stacks 0603: the space-level property may
already be tested on the diagrams whose ambient test space is an affine scheme, and those are
diagrams the scheme-level property covers.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map`: a scheme-level
  universal first-order thickening of objects of the site is a space-level universal first-order
  thickening of the algebraic spaces they represent.

## Implementation notes

**How the test diagram is made representable.** Given an affine test space `T'`, the
`AlgebraicGeometry.Space.IsAffineSpace` hypothesis supplies an object `T₀` of the site with
affine underlying scheme and an isomorphism `eT' : T'.obj ≅ yoneda.obj T₀`. Reading `eT'.inv`
as an étale chart of `T'` and feeding it to
`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback` produces an object `U₀` of
the site, a closed immersion `j : U₀ ⟶ T₀` which is a first-order thickening of schemes, and a
cartesian square identifying `yoneda.obj U₀` with the pullback of the inclusion of `T` along
`eT'.inv`. Since `eT'.inv` is an isomorphism that pullback is `T` itself, which is what
`isIso_fst_of_chart_pullback_of_iso` below records; so the whole test diagram is the Yoneda
image of a diagram of the site.

**How the morphisms of the diagram become morphisms of the site.** The datum `a` lands in the
range of `yoneda.map i`, and `CategoryTheory.Subfunctor.toRange` is an isomorphism onto that
range because `yoneda.map i` is a monomorphism — the underlying morphism of schemes is a closed
immersion, hence so is `yoneda.map i`, hence it is a monomorphism. Composing with its inverse
turns `a` into a morphism `yoneda.obj U₀ ⟶ yoneda.obj V`, and `b` into a morphism
`yoneda.obj T₀ ⟶ yoneda.obj U`; both descend to the site because the Yoneda embedding is fully
faithful.

**How the lift returns.** The scheme-level universal property produces a morphism of schemes
`T₀ ⟶ V'`, not a morphism of the site: the site's inclusion into schemes is faithful but not
full, since a morphism of the site must commute with the structure morphisms to `S`. What
supplies the missing compatibility is the second equation of the lift, that it lies over `U`;
`AlgebraicGeometry.Space.exists_hom_of_map_comp_eq` turns exactly that equation into a morphism
of the site. This is why the lift is transported along the structure morphism rather than by
fullness.

**Faithfulness does the bookkeeping.** Every equation between morphisms of the site below is
proved by exhibiting the corresponding equation of presheaves or of schemes and appealing to
faithfulness of `CategoryTheory.yoneda` or of `AlgebraicGeometry.BigFppfOver.toScheme`. No
equation is proved by unfolding either functor. The identity `key` isolates the one equation
that both halves of the unique-existence statement need, so that the existence half and the
uniqueness half each use it once.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0603](https://stacks.math.columbia.edu/tag/0603)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The test thickening of an affine test space is representable -/

/-- The chart pullback of a thickening along an isomorphism recovers the thickening itself: in
a cartesian square over an isomorphism the opposite leg is an isomorphism too. -/
private theorem isIso_fst_of_chart_pullback_of_iso
    {T' : AlgebraicSpaces B S hS} {T₀ : BigFppfOver B S hS} (T : Subfunctor T'.obj)
    (e : T'.obj ≅ yoneda.obj T₀) {U₀ : BigFppfOver B S hS} {j : U₀ ⟶ T₀}
    {q : yoneda.obj U₀ ⟶ T.toFunctor} (hpb : IsPullback q (yoneda.map j) T.ι e.inv) :
    IsIso q := by
  have hpb' : IsPullback (𝟙 T.toFunctor) (T.ι ≫ e.hom) T.ι e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hfst : (IsPullback.isoIsPullback T.toFunctor (yoneda.obj T₀) hpb hpb').hom ≫
      𝟙 T.toFunctor = q :=
    IsPullback.isoIsPullback_hom_fst T.toFunctor (yoneda.obj T₀) hpb hpb'
  rw [Category.comp_id] at hfst
  exact hfst ▸ inferInstance

/-- The Yoneda image of a closed immersion of the site is a monomorphism of presheaves, so the
comparison with its range is an isomorphism. -/
private theorem isIso_toRange_yoneda_map {V V' : BigFppfOver B S hS} (i : V ⟶ V')
    (hi : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)) :
    IsIso (Subfunctor.toRange (yoneda.map i)) := by
  have hclosed : IsClosedImmersion B S hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hi
  have : Mono (yoneda.map i) := mono_of_isClosedImmersion B S hS (yoneda.map i) hclosed
  infer_instance

/-! ### The bridge -/

/-- **A scheme-level universal first-order thickening represents a space-level one.** Let
`i : V ⟶ V'` and `p : V' ⟶ U` be morphisms of the big fppf category over `S` whose underlying
morphisms of schemes make `V ⟶ V'` a universal first-order thickening of `V` over `U`. Then the
range of `yoneda.map i` is a universal first-order thickening of the algebraic space represented
by `V` over the algebraic space represented by `U`.

The space-level universal property is formally stronger than the scheme-level one, because its
test objects are arbitrary algebraic spaces over `S` rather than schemes. Stacks 0603 closes the
gap: by `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_iff_affine_lifting` it is
enough to test the diagrams whose ambient test space is an affine scheme, and such a diagram is
the Yoneda image of a diagram of the site, on which the scheme-level property applies. -/
theorem isUniversalFirstOrderThickening_range_yoneda_map
    {V V' U : BigFppfOver B S hS} (i : V ⟶ V') (p : V' ⟶ U)
    {hBase : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj U}
    (ht : Stacks.Thickenings.IsUniversalFirstOrderThickening hBase
      ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map p)) :
    IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) ((schemeSpaceFunctor B S hS).map p) := by
  classical
  -- The inclusion is a square-zero closed immersion of the site, hence a first-order
  -- thickening of the algebraic spaces its source and target represent.
  have hiSZ : IsSquareZeroClosedImmersion B S hS i :=
    ⟨ht.isFirstOrderThickening.1, ht.isFirstOrderThickening.2⟩
  have hfirst : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj V')
      (Subfunctor.range (yoneda.map i)) :=
    isFirstOrderThickening_range_yoneda_map B S hS i hiSZ
  -- The comparison with the range is invertible; name an inverse and the equation that says
  -- it composes with the Yoneda image of the inclusion to the inclusion of the range.
  obtain ⟨tr, _, htr2⟩ := (isIso_toRange_yoneda_map B S hS i hiSZ.1).out
  have htrι : tr ≫ yoneda.map i = (Subfunctor.range (yoneda.map i)).ι := by
    simpa [Subfunctor.toRange_ι] using htr2 =≫ (Subfunctor.range (yoneda.map i)).ι
  rw [isUniversalFirstOrderThickening_iff_affine_lifting B S hS _ _ hfirst]
  intro T' hT' T hT a b hcomm
  simp only [schemeSpaceFunctor_map_hom] at hcomm ⊢
  -- Name the test morphism to the base at the representable presheaf, so that every equation
  -- below is stated at one and the same type.
  obtain ⟨b₀, hb₀⟩ : ∃ x : T'.obj ⟶ yoneda.obj U, b = x := ⟨b, rfl⟩
  rw [hb₀] at hcomm ⊢
  obtain ⟨T₀, _hT₀aff, ⟨eT'⟩⟩ := hT'
  -- Read `eT'.inv` as an étale chart of `T'` and pull the thickening back along it.
  have heE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf eT'.inv :=
    presheaf_etale_of_isEtale B S hS (isEtale_of_iso B S hS eT'.symm)
  obtain ⟨U₀, j, q, hpb, hjFO⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hT T₀ eT'.inv heE
  have hqiso : IsIso q := isIso_fst_of_chart_pullback_of_iso B S hS T eT' hpb
  have hjScheme : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map j) := ⟨hjFO.1, hjFO.2⟩
  -- Descend `a` and `b` to morphisms of the site.
  obtain ⟨α, hαmap⟩ := yoneda.map_surjective (q ≫ a ≫ tr)
  obtain ⟨β, hβb⟩ := yoneda.map_surjective (eT'.inv ≫ b₀)
  -- The Yoneda image of the descended `a`, read back through the range comparison.
  have hright : yoneda.map (α ≫ i) = q ≫ a ≫ (Subfunctor.range (yoneda.map i)).ι := by
    rw [Functor.map_comp, hαmap, Category.assoc, Category.assoc a tr]
    exact congrArg (fun z => q ≫ a ≫ z) htrι
  -- The one identity both halves of the conclusion need: an equation of the site on the left,
  -- the first lift equation of the test diagram on the right.
  have key : ∀ δ : T₀ ⟶ V', yoneda.map (j ≫ δ) = yoneda.map (α ≫ i) ↔
      T.ι ≫ eT'.hom ≫ yoneda.map δ = a ≫ (Subfunctor.range (yoneda.map i)).ι := by
    intro δ
    have hleft : yoneda.map (j ≫ δ) = q ≫ T.ι ≫ eT'.hom ≫ yoneda.map δ := by
      rw [Functor.map_comp, ← Category.assoc q, hpb.w, Category.assoc, eT'.inv_hom_id_assoc]
    rw [hleft, hright]
    exact ⟨fun hδ ↦ (cancel_epi q).1 hδ, fun hδ ↦ by rw [hδ]⟩
  -- Compatibility of the descended diagram, first in the site and then in schemes.
  have hcompatSite : j ≫ β = α ≫ i ≫ p := by
    refine Yoneda.fullyFaithful.map_injective ?_
    rw [← Category.assoc α i p, yoneda.map_comp (α ≫ i) p, hright, yoneda.map_comp j β, hβb,
      ← reassoc_of% hpb.w]
    exact congrArg (q ≫ ·) (hcomm.trans (Category.assoc _ _ _).symm)
  have hcompat : (BigFppfOver.toScheme B S hS).map j ≫ (BigFppfOver.toScheme B S hS).map β =
      (BigFppfOver.toScheme B S hS).map α ≫ hBase := by
    rw [← Functor.map_comp, hcompatSite, Functor.map_comp, Functor.map_comp, ht.inclusion_toBase]
  -- The scheme-level universal property, then the lift read back into the site.
  obtain ⟨cS, hcS, hcSu⟩ := ht.existsUnique_lift ((BigFppfOver.toScheme B S hS).map j)
    hjScheme ((BigFppfOver.toScheme B S hS).map α) ((BigFppfOver.toScheme B S hS).map β) hcompat
  obtain ⟨γ, hγmap, hγp⟩ := exists_hom_of_map_comp_eq p (k := β) (ρ := cS) hcS.2
  -- An equation of the site is the same as its image in schemes.
  have hsch : ∀ {X Y : BigFppfOver B S hS} (f g : X ⟶ Y),
      f = g ↔ (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g :=
    fun f g => ((BigFppfOver.toScheme B S hS).map_injective.eq_iff).symm
  have hγsite : j ≫ γ = α ≫ i := by
    rw [hsch, Functor.map_comp, Functor.map_comp, hγmap]
    exact hcS.1
  refine ⟨eT'.hom ≫ yoneda.map γ, ⟨(key γ).1 (congrArg _ hγsite), ?_⟩, ?_⟩
  · erw [Category.assoc, ← Functor.map_comp, hγp, hβb]
    exact eT'.hom_inv_id_assoc b₀
  · -- A competing lift descends to the site and is a competing scheme-level lift.
    intro c' hc'
    obtain ⟨γ', hγ'map⟩ := yoneda.map_surjective (eT'.inv ≫ c')
    have hγ'collapse : eT'.hom ≫ yoneda.map γ' = c' := by
      rw [hγ'map]
      exact eT'.hom_inv_id_assoc c'
    have hγ'p : γ' ≫ p = β := by
      refine Yoneda.fullyFaithful.map_injective ?_
      rw [Functor.map_comp, hγ'map]
      exact (Category.assoc _ _ _).trans ((congrArg (eT'.inv ≫ ·) hc'.2).trans hβb.symm)
    have hγγ' : γ' = γ := by
      refine (BigFppfOver.toScheme B S hS).map_injective ((hcSu _ ⟨?_, ?_⟩).trans hγmap.symm)
      · rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg _ (Yoneda.fullyFaithful.map_injective
          ((key γ').2 (by rw [hγ'collapse]; exact hc'.1)))
      · rw [← Functor.map_comp, hγ'p]
    exact hγ'collapse.symm.trans (congrArg (fun z => eT'.hom ≫ yoneda.map z) hγγ')

end AlgebraicGeometry.Space

end
