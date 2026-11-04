module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitDecompositionRestriction

/-!
# The presheaf-level assembly of the étale splitting of Stacks 082H

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitQuasiFiniteReduction.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitDecompositionRestriction.lean` carry out the
first three paragraphs of the proof of Stacks 082H and deliver, over an object `Zu` of the big
fppf category over `S` étale over an affine object `Y₀`, an object `Z₁` of that category, a
morphism `ζ : Z₁ ⟶ Zu` which is **finite** on underlying schemes, and an **open immersion** `θ`
from the underlying scheme of `Z₁` into the fibre product `Z ×_{Y₀} Zu` of schemes, where
`b : h_Z ⟶ P` is an étale chart of the algebraic space `P` under consideration and `τ : Z ⟶ Y₀`
underlies `b ≫ k₁`.

What `AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` consumes is
not `θ` but an **étale morphism of presheaves** `z : h_{Z₁} ⟶ Zu ×_{Y₀} P` whose composite with
the projection to `h_{Zu}` is `h_ζ`, together with its two conditions on the fibre over the
distinguished point. This file produces the morphism, and reduces the two conditions on the
fibre to conditions on morphisms of schemes.

The construction uses that the big fppf category over `S` has fibre products and that its
functor to schemes preserves them (Stacks 021U,
`StacksFrontier/AlgebraicGeometry/Topologies/Fppf/FibreProducts.lean`): the scheme `Z ×_{Y₀} Zu` is
therefore the underlying scheme of an object `Z ×_{Y₀} Zu` *of the category*, so `θ` lifts to a
morphism of the category and its Yoneda image is available. The functor to schemes is **not**
full, so the lift is not immediate; it is performed by
`AlgebraicGeometry.Space.exists_hom_toScheme_map_eq_of_comp`, which uses that the inclusion of
the size-bounded schemes is fully faithful and that a morphism of a slice category is a morphism
of the underlying category commuting with the structure morphisms.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_hom_toScheme_map_eq_of_comp` lifts a morphism of schemes
  between the underlying schemes of two objects of the big fppf category over `S` to a morphism
  of that category, given that it is compatible with morphisms of the category to a common
  target.
* `AlgebraicGeometry.Space.exists_isPullback_comparison_of_etaleChart` identifies the Yoneda
  image of the fibre product `Z ×_{Y₀} Zu` of the category as the base change of the chart
  `b` along the projection `Zu ×_{Y₀} P ⟶ P`: there is a comparison morphism
  `c : h_{Z ×_{Y₀} Zu} ⟶ Zu ×_{Y₀} P` sitting in a cartesian square with `b`, whose composite
  with the projection to `h_{Zu}` is the Yoneda image of the second projection.
* `AlgebraicGeometry.Space.exists_etale_comparison_of_etale_site_hom` is the assembly in its
  site-level form: for a morphism `η : Z₁ ⟶ Z ×_{Y₀} Zu` of the category which is étale on
  underlying schemes, the composite `h_η ≫ c` is an étale morphism of presheaves.
* `AlgebraicGeometry.Space.exists_etale_site_hom_of_openImmersion` produces that `η` from the
  open immersion `θ`, together with the identity relating the two.
* `AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion` is the assembly in the form
  the open immersion `θ` is delivered in: an **étale** morphism `z : h_{Z₁} ⟶ Zu ×_{Y₀} P` of
  presheaves whose composite with the projection to `h_{Zu}` is `h_ζ`, together with the
  morphism `ξ : Z₁ ⟶ Z` of the category through which its composite with the projection to `P`
  factors as `h_ξ ≫ b`, and whose underlying morphism of schemes is `θ ≫ pullback.fst`.
* `AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion_pullback` transports that
  along the canonical isomorphism `Zu ×_{Y₀} (Y₀ ×_Y X) ≅ Zu ×_Y X`, which is the form in which
  the conclusion of Stacks 082H is stated.
* `AlgebraicGeometry.Space.exists_schemePoint_of_isPullback_yoneda` lifts a compatible pair of
  points across the cartesian square of
  `AlgebraicGeometry.Space.exists_isPullback_comparison_of_etaleChart`: a point of `Zu ×_{Y₀} P`
  and a point of the scheme `Z` with the same image in `|P|` come from a point of the scheme
  `Z ×_{Y₀} Zu`. This is Tag 03H4 together with clause (1) of Tag 03BX.
* `AlgebraicGeometry.Space.forall_exists_pointsMap_eq_of_fibre_schemePoints` reduces the first
  condition on the fibre — every point of `|V| ⟶ |U|` over the distinguished point maps to one
  of the `xᵢ` — to the scheme-level condition that every point of `|Z₁|` over the distinguished
  point of `|Zu|` maps to one of the prescribed points of `|Z|`.
* `AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range` reduces the second
  condition on the fibre — no point of `|W|` over the distinguished point maps to an `xᵢ` — to
  the scheme-level condition that every point of `|Z ×_{Y₀} Zu|` over the distinguished point
  lying over a prescribed point of `|Z|` is in the image of `|Z₁|`.
* `AlgebraicGeometry.Space.mem_range_pointsMap_comp_iso_iff` transports that image statement
  along the isomorphism identifying `Zu ×_{Y₀} (Y₀ ×_Y X)` with `Zu ×_Y X`.

## Implementation notes

The comparison morphism `c` is produced by `CategoryTheory.IsPullback.of_bot'`, which both
constructs the morphism as a lift against the defining square of `Zu ×_{Y₀} P` and proves that
the resulting upper square is cartesian. The outer square it consumes is the Yoneda image of the
defining square of the fibre product `Z ×_{Y₀} Zu` of the category, rewritten along
`h_τ = b ≫ k₁`; `CategoryTheory.yoneda` preserves all limits, so no hypothesis is needed for
that step.

Étaleness of `z` is established in the relatively representable form
`CategoryTheory.MorphismProperty.presheaf` and only then converted, because that form is what is
stable under base change and composition. The two conversions are
`AlgebraicGeometry.Space.presheafEtale_of_isEtale_yoneda` and
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale`.

The assembly is stated twice because the two point-level reductions need the factorisation of
`z` through `h_{Z ×_{Y₀} Zu}`, which the form taking `θ` as its input cannot expose: two points
of a fibre product of schemes with the same pair of images need not be equal, so the morphism
`η` of the category is not recoverable from its two projections and has to be carried.

Nothing here carries the tag 082H, and nothing here is the tag. Both scheme-level conditions
that the two point-level reductions consume are conclusions of Tag 02LN transported along the
restriction of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitDecompositionRestriction.lean`, which does not
carry them; so the conclusion of Stacks 082H is not assembled here either.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting a morphism of schemes to the big fppf category over `S` -/

/-- **A morphism of underlying schemes compatible with two morphisms to a common object lifts to
the big fppf category over `S`.** Let `d : C ⟶ D` and `a : A ⟶ D` be morphisms of the big fppf
category over `S` and let `h` be a morphism from the underlying scheme of `A` to that of `C`
whose composite with the morphism of schemes underlying `d` is the one underlying `a`. Then `h`
is the morphism of schemes underlying a morphism `A ⟶ C` of the category.

The functor `AlgebraicGeometry.BigFppfOver.toScheme` is faithful but **not** full — the category
is a slice, so a morphism of it is a morphism of size-bounded schemes commuting with the
structure morphisms to `S` — which is why the compatibility hypothesis is needed. The inclusion
of the size-bounded schemes into schemes is fully faithful, so `h` comes from a morphism `h₀` of
size-bounded schemes; the hypothesis gives `h₀ ≫ d.left = a.left` by faithfulness, and the
required identity `h₀ ≫ C.hom = A.hom` then follows from the two slice identities
`d.left ≫ D.hom = C.hom` and `a.left ≫ D.hom = A.hom`. -/
theorem exists_hom_toScheme_map_eq_of_comp {A C D : BigFppfOver B S hS} (d : C ⟶ D) (a : A ⟶ D)
    (h : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hcomm : h ≫ (BigFppfOver.toScheme B S hS).map d = (BigFppfOver.toScheme B S hS).map a) :
    ∃ e : A ⟶ C, (BigFppfOver.toScheme B S hS).map e = h := by
  have hh₀ : B.inclusion.map (B.inclusion.preimage h) = h := B.inclusion.map_preimage h
  have hfac : B.inclusion.preimage h ≫ d.left = a.left := by
    refine B.inclusion.map_injective ?_
    rwa [Functor.map_comp, hh₀]
  refine ⟨Over.homMk (B.inclusion.preimage h) ?_, hh₀⟩
  rw [← Over.w d, ← Category.assoc, hfac, Over.w a]

/-! ### The fibre product of the category as a base change of the chart -/

/-- **The Yoneda image of `Z ×_{Y₀} Zu` is the base change of the chart along the projection.**
Let `k₁ : P ⟶ h_{Y₀}` be a morphism of presheaves on the big fppf category over `S`, let
`b : h_Z ⟶ P` be a morphism with `h_τ = b ≫ k₁` for a morphism `τ : Z ⟶ Y₀` of the category, and
let `ν : Zu ⟶ Y₀` be a morphism of the category. Then there is a morphism
`c : h_{Z ×_{Y₀} Zu} ⟶ Zu ×_{Y₀} P` of presheaves such that the square with `h` of the first
projection on top, `c` and `b` on its sides and the projection `Zu ×_{Y₀} P ⟶ P` along its
bottom is cartesian, and such that the composite of `c` with the projection to `h_{Zu}` is the
Yoneda image of the second projection.

Being cartesian over `b`, the morphism `c` inherits from `b` every property of morphisms of
presheaves obtained by `CategoryTheory.MorphismProperty.presheaf`, in particular étaleness. The
fibre product `Z ×_{Y₀} Zu` is taken in the big fppf category over `S`, which has fibre products
by Stacks 021U; `CategoryTheory.yoneda` preserves them, and the comparison morphism together
with the cartesian square is `CategoryTheory.IsPullback.of_bot'` applied to that Yoneda image and
to the defining square of `Zu ×_{Y₀} P`. -/
theorem exists_isPullback_comparison_of_etaleChart
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ Zu Z : BigFppfOver B S hS}
    (k₁ : P ⟶ yoneda.obj Y₀) (ν : Zu ⟶ Y₀) {τ : Z ⟶ Y₀} (b : yoneda.obj Z ⟶ P)
    (hτ : yoneda.map τ = b ≫ k₁) :
    ∃ c : yoneda.obj (pullback τ ν) ⟶ pullback (yoneda.map ν) k₁,
      IsPullback (yoneda.map (pullback.fst τ ν)) c b (pullback.snd (yoneda.map ν) k₁) ∧
      c ≫ pullback.fst (yoneda.map ν) k₁ = yoneda.map (pullback.snd τ ν) := by
  have hsq1 : IsPullback (yoneda.map (pullback.fst τ ν)) (yoneda.map (pullback.snd τ ν))
      (b ≫ k₁) (yoneda.map ν) := by
    rw [← hτ]
    exact (IsPullback.of_hasPullback τ ν).map yoneda
  have ht : IsPullback (pullback.snd (yoneda.map ν) k₁) (pullback.fst (yoneda.map ν) k₁) k₁
      (yoneda.map ν) := (IsPullback.of_hasPullback (yoneda.map ν) k₁).flip
  exact ⟨_, IsPullback.of_bot' hsq1 ht, ht.lift_snd _ _ _⟩

/-! ### The étale morphism of presheaves, in its site-level form -/

/-- **A morphism of the category into `Z ×_{Y₀} Zu` which is étale on underlying schemes induces
an étale morphism of presheaves into `Zu ×_{Y₀} P`.** In the situation of
`AlgebraicGeometry.Space.exists_isPullback_comparison_of_etaleChart`, with `b` étale, the
composite of the Yoneda image of a morphism `η : Z₁ ⟶ Z ×_{Y₀} Zu` of the category which is
étale on underlying schemes with the comparison morphism `c` is an étale morphism of presheaves.

The comparison morphism and the cartesian square are returned as well, because a consumer which
needs to lift points across the square — through
`AlgebraicGeometry.Space.exists_schemePoint_of_isPullback_yoneda` — needs the square and not only
the composite.

Étaleness is proved in the relatively representable form
`CategoryTheory.MorphismProperty.presheaf`: the Yoneda image of `η` has it by clause (1) of
Stacks 03FR in the form `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, the
comparison morphism has it as a base change of `b`, and the form is multiplicative. -/
theorem exists_etale_comparison_of_etale_site_hom
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ Zu Z₁ Z : BigFppfOver B S hS}
    (k₁ : P ⟶ yoneda.obj Y₀) (ν : Zu ⟶ Y₀) {τ : Z ⟶ Y₀} {b : yoneda.obj Z ⟶ P}
    (hbE : IsEtale B S hS b) (hτ : yoneda.map τ = b ≫ k₁) (η : Z₁ ⟶ pullback τ ν)
    (hηE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map η)) :
    ∃ c : yoneda.obj (pullback τ ν) ⟶ pullback (yoneda.map ν) k₁,
      IsPullback (yoneda.map (pullback.fst τ ν)) c b (pullback.snd (yoneda.map ν) k₁) ∧
      c ≫ pullback.fst (yoneda.map ν) k₁ = yoneda.map (pullback.snd τ ν) ∧
      IsEtale B S hS (yoneda.map η ≫ c) := by
  obtain ⟨c, hcsq, hcfst⟩ := exists_isPullback_comparison_of_etaleChart B S hS k₁ ν b hτ
  refine ⟨c, hcsq, hcfst, ?_⟩
  have hmul := isMultiplicative_presheaf_etale B S hS
  refine isEtale_of_presheaf_etale B S hS
    (MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ η).2 hηE) ?_)
  exact presheaf_of_isPullback B S hS hcsq (presheafEtale_of_isEtale_yoneda B S hS b hbE)

/-- **The open immersion of Stacks 082H is the morphism of schemes underlying a morphism of the
category into the fibre product `Z ×_{Y₀} Zu` of the category.** Let `ν : Zu ⟶ Y₀`,
`τ : Z ⟶ Y₀` and `ζ : Z₁ ⟶ Zu` be morphisms of the big fppf category over `S` and let `θ` be an
open immersion from the underlying scheme of `Z₁` into the fibre product of the underlying
schemes of `τ` and `ν` whose composite with the second projection is the morphism of schemes
underlying `ζ`. Then there is a morphism `η : Z₁ ⟶ Z ×_{Y₀} Zu` of the category which is étale on
underlying schemes, whose composite with the second projection is `ζ`, and whose underlying
morphism of schemes followed by the comparison isomorphism
`CategoryTheory.Limits.PreservesPullback.iso` is `θ`.

This is the sentence of the proof of Stacks 082H which replaces the scheme `Z_1` by an object of
the site. The lift is `AlgebraicGeometry.Space.exists_hom_toScheme_map_eq_of_comp` applied to `θ`
corrected by the inverse of the comparison isomorphism, whose compatibility hypothesis is
supplied by the factorisation of `θ` through the second projection; the lifted morphism is étale
on underlying schemes because an open immersion is and an isomorphism is. -/
theorem exists_etale_site_hom_of_openImmersion {Y₀ Zu Z₁ Z : BigFppfOver B S hS} (ν : Zu ⟶ Y₀)
    (τ : Z ⟶ Y₀) (ζ : Z₁ ⟶ Zu)
    (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
      pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν))
    (hθoi : _root_.AlgebraicGeometry.IsOpenImmersion θ)
    (hθfac : θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
      ((BigFppfOver.toScheme B S hS).map ν) = (BigFppfOver.toScheme B S hS).map ζ) :
    ∃ η : Z₁ ⟶ pullback τ ν,
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map η) ∧
      η ≫ pullback.snd τ ν = ζ ∧
      (BigFppfOver.toScheme B S hS).map η ≫
        (PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ν).hom = θ := by
  have hinvsnd : (PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ν).inv ≫
      (BigFppfOver.toScheme B S hS).map (pullback.snd τ ν) =
      pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [← PreservesPullback.iso_hom_snd, Iso.inv_hom_id_assoc]
  obtain ⟨η, hη⟩ := exists_hom_toScheme_map_eq_of_comp B S hS (pullback.snd τ ν) ζ
    (θ ≫ (PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ν).inv)
    (by rw [Category.assoc, hinvsnd, hθfac])
  refine ⟨η, ?_, (BigFppfOver.toScheme B S hS).map_injective ?_, ?_⟩
  · rw [hη]
    infer_instance
  · rw [Functor.map_comp, hη, Category.assoc, hinvsnd, hθfac]
  · rw [hη, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The étale morphism of presheaves produced by the open immersion -/

/-- **The open immersion of Stacks 082H yields an étale morphism of presheaves into the base
change.** Let `k₁ : P ⟶ h_{Y₀}` be a morphism of presheaves on the big fppf category over `S`,
let `b : h_Z ⟶ P` be étale with `h_τ = b ≫ k₁` for a morphism `τ : Z ⟶ Y₀` of the category, let
`ν : Zu ⟶ Y₀` and `ζ : Z₁ ⟶ Zu` be morphisms of the category, and let `θ` be an open immersion
from the underlying scheme of `Z₁` into the fibre product `Z ×_{Y₀} Zu` of schemes whose
composite with the second projection is the morphism of schemes underlying `ζ`. Then there are an
**étale** morphism `z : h_{Z₁} ⟶ Zu ×_{Y₀} P` of presheaves and a morphism `ξ : Z₁ ⟶ Z` of the
category such that

* the composite of `z` with the projection to `h_{Zu}` is `h_ζ`;
* the composite of `z` with the projection to `P` is `h_ξ ≫ b`;
* the morphism of schemes underlying `ξ` is `θ` followed by the first projection.

This is the presheaf-level assembly that
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` consumes, with the
first clause supplying its hypothesis `hζ`. The morphism `ξ` and the last two clauses are not
needed for that, but they are what
`AlgebraicGeometry.Space.forall_exists_pointsMap_eq_of_fibre_schemePoints` consumes to reduce the
first of its two conditions on the fibre over the distinguished point.

It is `AlgebraicGeometry.Space.exists_etale_comparison_of_etale_site_hom` applied to the morphism
of the category produced by `AlgebraicGeometry.Space.exists_etale_site_hom_of_openImmersion`. A
consumer which needs the second condition on the fibre should use those two results directly:
the factorisation of `z` through `h_{Z ×_{Y₀} Zu}` is not recoverable from this statement. -/
theorem exists_etale_yoneda_hom_of_openImmersion
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ Zu Z₁ Z : BigFppfOver B S hS}
    (k₁ : P ⟶ yoneda.obj Y₀) (ν : Zu ⟶ Y₀) {ζ : Z₁ ⟶ Zu} {τ : Z ⟶ Y₀}
    {b : yoneda.obj Z ⟶ P} (hbE : IsEtale B S hS b) (hτ : yoneda.map τ = b ≫ k₁)
    (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
      pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν))
    (hθoi : _root_.AlgebraicGeometry.IsOpenImmersion θ)
    (hθfac : θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
      ((BigFppfOver.toScheme B S hS).map ν) = (BigFppfOver.toScheme B S hS).map ζ) :
    ∃ (z : yoneda.obj Z₁ ⟶ pullback (yoneda.map ν) k₁) (ξ : Z₁ ⟶ Z),
      IsEtale B S hS z ∧
      z ≫ pullback.fst (yoneda.map ν) k₁ = yoneda.map ζ ∧
      z ≫ pullback.snd (yoneda.map ν) k₁ = yoneda.map ξ ≫ b ∧
      (BigFppfOver.toScheme B S hS).map ξ =
        θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) := by
  obtain ⟨η, hηE, hηsnd, hηθ⟩ :=
    exists_etale_site_hom_of_openImmersion B S hS ν τ ζ θ hθoi hθfac
  obtain ⟨c, hcsq, hcfst, hzE⟩ :=
    exists_etale_comparison_of_etale_site_hom B S hS k₁ ν hbE hτ η hηE
  refine ⟨yoneda.map η ≫ c, η ≫ pullback.fst τ ν, hzE, ?_, ?_, ?_⟩
  · rw [Category.assoc, hcfst, ← Functor.map_comp, hηsnd]
  · rw [Category.assoc, ← hcsq.w, Functor.map_comp, Category.assoc]
  · rw [Functor.map_comp, ← hηθ, Category.assoc, PreservesPullback.iso_hom_fst]

/-- **The étale morphism of presheaves into the base change `Zu ×_Y X`.** The form of
`AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion` in which the conclusion of
Stacks 082H is stated: the space being decomposed there is `U ×_Y X` for an étale morphism
`U ⟶ Y` of algebraic spaces, and `U = h_{Zu}` arises as `h_ν` followed by the étale
neighbourhood `g₀ : h_{Y₀} ⟶ Y` of the source's first paragraph, so the space in question is
`Zu ×_Y X` rather than the iterated base change `Zu ×_{Y₀} (Y₀ ×_Y X)`.

The two presheaves are identified by Mathlib's
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which is compatible with both projections;
an isomorphism of presheaves is étale, so the transported morphism is still étale. -/
theorem exists_etale_yoneda_hom_of_openImmersion_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {Y₀ Zu Z₁ Z : BigFppfOver B S hS} (g₀ : yoneda.obj Y₀ ⟶ Y)
    (ν : Zu ⟶ Y₀) {ζ : Z₁ ⟶ Zu} {τ : Z ⟶ Y₀}
    {b : yoneda.obj Z ⟶ pullback g₀ f} (hbE : IsEtale B S hS b)
    (hτ : yoneda.map τ = b ≫ pullback.fst g₀ f)
    (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
      pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν))
    (hθoi : _root_.AlgebraicGeometry.IsOpenImmersion θ)
    (hθfac : θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
      ((BigFppfOver.toScheme B S hS).map ν) = (BigFppfOver.toScheme B S hS).map ζ) :
    ∃ (z : yoneda.obj Z₁ ⟶ pullback (yoneda.map ν ≫ g₀) f) (ξ : Z₁ ⟶ Z),
      IsEtale B S hS z ∧
      z ≫ pullback.fst (yoneda.map ν ≫ g₀) f = yoneda.map ζ ∧
      z ≫ pullback.snd (yoneda.map ν ≫ g₀) f =
        yoneda.map ξ ≫ b ≫ pullback.snd g₀ f ∧
      (BigFppfOver.toScheme B S hS).map ξ =
        θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) := by
  obtain ⟨z, ξ, hzE, hzfst, hzsnd, hξ⟩ := exists_etale_yoneda_hom_of_openImmersion B S hS
    (pullback.fst g₀ f) ν hbE hτ θ hθoi hθfac
  refine ⟨z ≫ (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).hom, ξ,
    isEtale_comp B S hS hzE (isEtale_of_isIso B S hS _), ?_, ?_, hξ⟩
  · rwa [Category.assoc, pullbackRightPullbackFstIso_hom_fst]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc, hzsnd,
      Category.assoc]

/-! ### Lifting a compatible pair of points across the comparison square -/

/-- **A point of the base change and a point of the chart with the same image come from a point
of the fibre product of schemes.** Let the square with `h_ξ` on top, `c` and `b` on its sides and
`q` along its bottom be cartesian, with `ξ : Zν ⟶ Z` a morphism of the big fppf category over
`S`. Then for every point `p` of the lower-left corner and every point `a` of the underlying
scheme of `Z` whose image under `b` on points agrees with the image of `p` under `q`, there is a
point of the underlying scheme of `Zν` which `c` carries to `p` and whose image under the
morphism of schemes underlying `ξ` is `a`.

The surjectivity of the comparison map from the points of a fibre product of presheaves to the
fibre product of the point sets is Tag 03H4,
`AlgebraicGeometry.Space.exists_points_of_isPullback`; the passage between the points of a
represented presheaf and the points of the representing scheme is clause (1) of Tag 03BX,
`AlgebraicGeometry.Space.pointsEquivScheme`, and its naturality.

Applied to the cartesian square of
`AlgebraicGeometry.Space.exists_isPullback_comparison_of_etaleChart`, this is the step that turns
the second condition of Stacks 082H on the fibre over the distinguished point into a condition on
the fibre of a morphism of schemes: it is what produces a point of `Z ×_{Y₀} Zu` from a point of
`Zu ×_{Y₀} P` and a point of `Z` lying over the same point of `|P|`. -/
theorem exists_schemePoint_of_isPullback_yoneda
    {P Pν : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z Zν : BigFppfOver B S hS}
    (b : yoneda.obj Z ⟶ P) (q : Pν ⟶ P) (c : yoneda.obj Zν ⟶ Pν) (ξ : Zν ⟶ Z)
    (hc : IsPullback (yoneda.map ξ) c b q)
    (p : points B S hS Pν) (a : (BigFppfOver.toScheme B S hS).obj Z)
    (ha : pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a) =
      pointsMap B S hS Pν q p) :
    ∃ ω : (BigFppfOver.toScheme B S hS).obj Zν,
      pointsMap B S hS (yoneda.obj Zν) c ((pointsEquivScheme B S hS Zν).symm ω) = p ∧
      (BigFppfOver.toScheme B S hS).map ξ ω = a := by
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hc
    ((pointsEquivScheme B S hS Z).symm a) p ha
  refine ⟨pointsEquivScheme B S hS Zν w, ?_, ?_⟩
  · rwa [(pointsEquivScheme B S hS Zν).symm_apply_apply]
  · rw [← pointsEquivScheme_pointsMap_yoneda B S hS ξ w, hw₁,
      (pointsEquivScheme B S hS Z).apply_symm_apply]

/-! ### The two conditions on the fibre, reduced to conditions on schemes -/

/-- A point `w` of `h_A` is carried by `h_f` to the point corresponding to `t` iff the scheme
point corresponding to `w` is carried by `f` to `t`. -/
private theorem pointsMap_yoneda_map_eq_symm_iff {A C : BigFppfOver B S hS} (f : A ⟶ C)
    (w : points B S hS (yoneda.obj A)) (t : (BigFppfOver.toScheme B S hS).obj C) :
    pointsMap B S hS (yoneda.obj A) (yoneda.map f) w = (pointsEquivScheme B S hS C).symm t ↔
      (BigFppfOver.toScheme B S hS).map f (pointsEquivScheme B S hS A w) = t := by
  rw [Equiv.eq_symm_apply, pointsEquivScheme_pointsMap_yoneda]

/-- **The first condition of Stacks 082H on the fibre, from a condition on the fibre of a
morphism of schemes.** Let `ζ : Z₁ ⟶ Zu` and `ξ : Z₁ ⟶ Z` be morphisms of the big fppf category
over `S`, let `β : h_Z ⟶ G` be a morphism of presheaves, let `u'` be a point of the underlying
scheme of `Zu`, let `z₁, …, z_m` be points of the underlying scheme of `Z` and let
`x₁, …, x_n` be points of `|G|`. Suppose every point of the underlying scheme of `Z₁` which
`ζ` carries to `u'` is carried by `ξ` to one of the `z_j`, and that each `z_j` is carried by `β`
on points to one of the `xᵢ`. Then every point of `|h_{Z₁}|` which `h_ζ` carries to the point
corresponding to `u'` is carried by `h_ξ ≫ β` to one of the `xᵢ`.

This is the hypothesis `hVpts` of
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite`, reduced to a
condition on morphisms of schemes: the two factorisations
`z ≫ pullback.fst = h_ζ` and `z ≫ pullback.snd ≫ k₂ = h_ξ ≫ (b ≫ k₂)` of
`AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion` turn that hypothesis into this
conclusion with `β = b ≫ k₂`. The first of the two hypotheses here is the fibre clause of Tag
02LN transported along the restriction of the decomposition; the second is the identification of
the prescribed points of the chart with the preimage of the prescribed points of the space.

The passage between points of a represented presheaf and points of the representing scheme is
clause (1) of Tag 03BX and its naturality; no algebraicity and no property of `β` is used. -/
theorem forall_exists_pointsMap_eq_of_fibre_schemePoints
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Zu Z₁ Z : BigFppfOver B S hS} (ζ : Z₁ ⟶ Zu)
    (ξ : Z₁ ⟶ Z) (β : yoneda.obj Z ⟶ G) (u' : (BigFppfOver.toScheme B S hS).obj Zu)
    {m n : ℕ} (zz : Fin m → (BigFppfOver.toScheme B S hS).obj Z) (x : Fin n → points B S hS G)
    (hfib : ∀ t : (BigFppfOver.toScheme B S hS).obj Z₁,
      (BigFppfOver.toScheme B S hS).map ζ t = u' →
        ∃ j, (BigFppfOver.toScheme B S hS).map ξ t = zz j)
    (hzzx : ∀ j, ∃ i, pointsMap B S hS (yoneda.obj Z) β
      ((pointsEquivScheme B S hS Z).symm (zz j)) = x i) :
    ∀ w : points B S hS (yoneda.obj Z₁),
      pointsMap B S hS (yoneda.obj Z₁) (yoneda.map ζ) w =
          (pointsEquivScheme B S hS Zu).symm u' →
        ∃ i, pointsMap B S hS (yoneda.obj Z₁) (yoneda.map ξ ≫ β) w = x i := by
  intro w hw
  obtain ⟨j, hj⟩ := hfib (pointsEquivScheme B S hS Z₁ w)
    ((pointsMap_yoneda_map_eq_symm_iff B S hS ζ w u').1 hw)
  obtain ⟨i, hi⟩ := hzzx j
  refine ⟨i, ?_⟩
  rwa [pointsMap_comp_apply, (pointsMap_yoneda_map_eq_symm_iff B S hS ξ w _).2 hj]

/-- **The second condition of Stacks 082H on the fibre, from a condition on the image of a
morphism of schemes.** Let the square with `h_ξ` on top, `c` and `b` on its sides and `q` along
its bottom be cartesian, with `ξ : Zν ⟶ Z` a morphism of the big fppf category over `S`, and let
`η : Z₁ ⟶ Zν` be a morphism of the category. Let `p` be a point of the lower-left corner and `a`
a point of the underlying scheme of `Z` whose image under `b` on points agrees with the image of
`p` under `q`. If every point of the underlying scheme of `Zν` which `ξ` carries to `a` and `c`
carries to `p` lies in the image of the morphism of schemes underlying `η`, then `p` lies in the
image on points of `h_η ≫ c`.

This is the contrapositive form of the hypothesis `hWpts` of
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite`, reduced to a
condition on morphisms of schemes. In the application to Stacks 082H the square is the one of
`AlgebraicGeometry.Space.exists_isPullback_comparison_of_etaleChart`, `η` is the morphism of
`AlgebraicGeometry.Space.exists_etale_site_hom_of_openImmersion` and `h_η ≫ c` is the étale
morphism of `AlgebraicGeometry.Space.exists_etale_comparison_of_etale_site_hom`, so the
conclusion says that a point of `Zu ×_{Y₀} P` over the distinguished point which maps to one of
the prescribed points of `|P|` is in the image of `|Z₁|`, which is exactly what `hWpts` needs;
the hypothesis is then the clause of Tag 02LN about the complementary piece of the decomposition,
transported along the restriction, and `a` is supplied by the chart hitting the prescribed
points.

The point of `Zν` is produced by
`AlgebraicGeometry.Space.exists_schemePoint_of_isPullback_yoneda`; the remaining step is the
naturality of clause (1) of Tag 03BX. -/
theorem mem_range_pointsMap_of_schemePoint_range
    {P Pν : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z Zν Z₁ : BigFppfOver B S hS}
    (b : yoneda.obj Z ⟶ P) (q : Pν ⟶ P) (c : yoneda.obj Zν ⟶ Pν) (ξ : Zν ⟶ Z) (η : Z₁ ⟶ Zν)
    (hc : IsPullback (yoneda.map ξ) c b q)
    (p : points B S hS Pν) (a : (BigFppfOver.toScheme B S hS).obj Z)
    (ha : pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a) =
      pointsMap B S hS Pν q p)
    (hrange : ∀ ω : (BigFppfOver.toScheme B S hS).obj Zν,
      (BigFppfOver.toScheme B S hS).map ξ ω = a →
        pointsMap B S hS (yoneda.obj Zν) c ((pointsEquivScheme B S hS Zν).symm ω) = p →
          ω ∈ Set.range ((BigFppfOver.toScheme B S hS).map η)) :
    p ∈ Set.range (pointsMap B S hS (yoneda.obj Z₁) (yoneda.map η ≫ c)) := by
  obtain ⟨ω, hωc, hωξ⟩ :=
    exists_schemePoint_of_isPullback_yoneda B S hS b q c ξ hc p a ha
  obtain ⟨t, ht⟩ := hrange ω hωξ hωc
  refine ⟨(pointsEquivScheme B S hS Z₁).symm t, ?_⟩
  have hη : pointsMap B S hS (yoneda.obj Z₁) (yoneda.map η)
      ((pointsEquivScheme B S hS Z₁).symm t) = (pointsEquivScheme B S hS Zν).symm ω := by
    rw [pointsMap_yoneda_map_eq_symm_iff, Equiv.apply_symm_apply, ht]
  rwa [pointsMap_comp_apply, hη]

/-- **Transporting the image on points along an isomorphism of the target.** A point of `H` is in
the image on points of `z ≫ e.hom`, for an isomorphism `e : G ≅ H` of presheaves on the big fppf
category over `S`, exactly when its image under `e.inv` is in the image on points of `z`.

This is the step by which the conclusion of
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range`, which is about the
composite with the comparison morphism into the iterated base change `Zu ×_{Y₀} (Y₀ ×_Y X)`,
becomes a statement about the morphism into `Zu ×_Y X` that
`AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion_pullback` produces — and hence
about the hypothesis `hWpts` of
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` in the form Stacks
082H needs it. -/
theorem mem_range_pointsMap_comp_iso_iff
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : F ⟶ G) (e : G ≅ H) (p : points B S hS H) :
    p ∈ Set.range (pointsMap B S hS F (z ≫ e.hom)) ↔
      pointsMap B S hS H e.inv p ∈ Set.range (pointsMap B S hS F z) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    rw [pointsMap_comp_apply, ← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id]
    rfl
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [pointsMap_comp_apply, hw, ← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id]
    rfl

end AlgebraicGeometry.Space

end
