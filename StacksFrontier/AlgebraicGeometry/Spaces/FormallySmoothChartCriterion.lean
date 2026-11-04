module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocally
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# The étale-chart criterion for formal smoothness of a morphism of algebraic spaces

[Stacks Project, Tag 061K] states that for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S` the following are equivalent: (1) `f` is formally smooth; (2) the scheme morphism
`ψ` in *every* commuting square of étale scheme charts of `f` is formally smooth, in the sense
of the infinitesimal lifting property `Stacks.Smooth.FormallySmoothScheme`; (3) the same for
*one* such square with surjective charts.

This file proves the implications (1) ⟹ (2) and (1) ⟹ (3) with formal smoothness of `ψ` read
on affine opens — `Stacks.Smooth.FormallySmoothAffineLocally`, which is condition (3) of
[Stacks Project, Tag 0D0F] — and deduces (1) ⟹ (2), (1) ⟹ (3) verbatim from the single
scheme-level implication (3) ⟹ (1) of Tag 0D0F, which is
`Stacks.Smooth.formallySmooth_of_formallySmooth_appLE`. Both implications are therefore
unconditional. The biconditionals of Tag 061K are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean`, which is where
the tag is registered; nothing here is tagged `061K`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Smooth.formallySmoothAffineLocally_of_exists_lift_of_size_lt`: a morphism of schemes
  of size below a cardinal `κ` which has the lifting property against first-order thickenings
  of affine schemes of size below `κ` is affine-locally formally smooth. This is the formal
  smoothness half of `Stacks.Smooth.smooth_of_exists_lift_of_size_lt` with the local finite
  presentation hypothesis removed.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothAffineLocally`: if `f` is
  formally smooth then the scheme morphism in every commuting square of étale scheme charts of
  `f` is affine-locally formally smooth. This is [Stacks Project, Tag 061K] (1) ⟹ (2) with
  condition (2) read as condition (3) of [Stacks Project, Tag 0D0F].
* `AlgebraicGeometry.Space.formallySmoothScheme_map_of_formallySmooth_of_isAffineHom`: in a
  commuting square of étale scheme charts of a formally smooth `f` whose scheme morphism is
  *affine*, that scheme morphism is formally smooth in the sense of
  `Stacks.Smooth.FormallySmoothScheme`. This is the instance of condition (2) of
  [Stacks Project, Tag 061K] that is reached with no extra hypothesis.
* `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart`: the
  every-chart condition implies the one-surjective-chart condition, for an arbitrary property
  of morphisms of schemes. This is the implication (1) ⟹ (2) of [Stacks Project, Tag 03MJ],
  which needs no étale locality of the property.
* `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally`: the same
  conclusion on one commuting square of étale charts whose chart of the source is surjective,
  which is [Stacks Project, Tag 061K] (1) ⟹ (3) in the same reading.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothScheme'` and
  `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothScheme'`: conditions (2)
  and (3) of [Stacks Project, Tag 061K] verbatim, from condition (1), through the implication
  (3) ⟹ (1) of [Stacks Project, Tag 0D0F].

## Implementation notes

The obstruction to condition (2) of Tag 061K was recorded as a question of *size*:
`AlgebraicGeometry.Space.FormallySmooth` can only be applied to square-zero closed immersions
of affine *objects of the site*, and every big fppf site omits affine schemes, whereas
`Stacks.Smooth.FormallySmoothScheme` quantifies over first-order thickenings of all affine
schemes. That gap is closed here, and it is closed without any finiteness hypothesis on `ψ`:
formal smoothness of an algebra is detected by the *single* square-zero extension cut out by
the square of the kernel of a polynomial presentation, which is
`Stacks.Smooth.formallySmooth_of_exists_section_of_mk_lt`, and that extension has cardinality
at most `max ℵ₀ (max #Γ(V, V₀) #Γ(U, W))`, hence below the cutoff of the site. So the
implication (1) ⟹ (2) is not obstructed by size at all; what remains is exactly the
scheme-level implication (3) ⟹ (1) of Tag 0D0F, that a morphism of schemes inducing formally
smooth ring maps on affine opens has the infinitesimal lifting property. That implication is
`Stacks.Smooth.formallySmooth_of_formallySmooth_appLE` of
`StacksFrontier/AlgebraicGeometry/Smooth/FormallySmoothTFAE.lean` — the torsor of local lifts
together with the vanishing of `H¹` of a quasi-coherent sheaf on an affine scheme — and it is
applied directly in the last two results, which therefore carry no hypothesis beyond formal
smoothness of `f`. The only bookkeeping needed is that
`Stacks.Smooth.FormallySmoothAffineLocally` and the `appLE` form that implication consumes are
interchanged by `Stacks.Smooth.formallySmoothAffineLocally_iff_appLE`.

`Stacks.Smooth.smooth_of_exists_lift_of_size_lt` is the conjunction of
`Stacks.Smooth.formallySmoothAffineLocally_of_exists_lift_of_size_lt` with local finite
presentation, through `Stacks.Smooth.smooth_iff_formallySmoothAffineLocally`; it predates this
file and is left unchanged.

The converse implication (3) ⟹ (1) of Tag 061K is the torsor argument of
[Stacks Project, Tag 04AM] step (II) and is not approached here; it is approached in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean`, where step (I),
the existence of étale-local lifts, is proved and the torsor triviality is what is left.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 061H](https://stacks.math.columbia.edu/tag/061H)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal

universe u

namespace Stacks.Smooth

-- `_root_` is needed: a transitive import of
-- `StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE` declares the namespace
-- `Stacks.Smooth.AlgebraicGeometry`, which an unqualified `open AlgebraicGeometry` picks up here.
open _root_.AlgebraicGeometry

/-- **Affine-local formal smoothness from thickenings of bounded size.** A morphism of schemes
of size below `κ` which has the lifting property against first-order thickenings of affine
schemes of size below `κ` induces a formally smooth ring map on sections over every pair of
affine opens, that is, is affine-locally formally smooth.

This is `Stacks.Smooth.smooth_of_exists_lift_of_size_lt` with the local finite presentation
hypothesis removed and the conclusion weakened accordingly: by
`Stacks.Smooth.smooth_iff_formallySmoothAffineLocally` that lemma is this one together with
local finite presentation. The reduction to bounded size is
`Stacks.Smooth.formallySmooth_of_exists_section_of_mk_lt`, which needs only the thickening of a
polynomial presentation of the sections over an affine chart; that thickening is the spectrum
of a ring of cardinality at most `max ℵ₀ (max #Γ(S, V₀) #Γ(X, W))`, and both of those are at
most the size of the respective scheme by `AlgebraicGeometry.Scheme.mk_sections_le_size`. -/
theorem formallySmoothAffineLocally_of_exists_lift_of_size_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    {X S : Scheme.{u}} (f : X ⟶ S) (hX : X.size < κ) (hS : S.size < κ)
    (H : ∀ (T T' : Scheme.{u}), IsAffine T → IsAffine T' → T.size < κ → T'.size < κ →
      ∀ i : T ⟶ T', Thickenings.IsFirstOrderThickening i →
      ∀ (g : T ⟶ X) (k : T' ⟶ S), g ≫ f = i ≫ k →
        ∃ τ : T' ⟶ X, i ≫ τ = g ∧ τ ≫ f = k) :
    FormallySmoothAffineLocally f := by
  have hspec : ∀ Rr : CommRingCat.{u}, #Rr < κ → (Spec Rr).size < κ := by
    intro Rr hRr
    rw [Scheme.size_of_isAffine]
    exact max_lt hκ (lt_of_eq_of_lt (Cardinal.mk_congr
      (Scheme.ΓSpecIso Rr).commRingCatIsoToRingEquiv.toEquiv) hRr)
  rw [formallySmoothAffineLocally_iff_appLE]
  intro V₀ W e
  let instAlg : Algebra Γ(S, V₀.1) Γ(X, W.1) := (f.appLE V₀.1 W.1 e).hom.toAlgebra
  have hW : #Γ(X, W.1) < κ := lt_of_le_of_lt (X.mk_sections_le_size W) hX
  refine formallySmooth_of_exists_section_of_mk_lt hκ
    (lt_of_le_of_lt (S.mk_sections_le_size V₀) hS) hW ?_
  intro Q _ _ π hπ hπ2 hQ
  obtain ⟨s, hs₁, hs₂⟩ := exists_appLE_section_of_exists_lift f V₀.2 W.2 e
    (Q := CommRingCat.of Q) (CommRingCat.ofHom π.toRingHom) hπ hπ2
    (CommRingCat.ofHom (algebraMap Γ(S, V₀.1) Q))
    (CommRingCat.hom_ext (RingHom.ext fun r => π.commutes r))
    (fun g k hgk => H _ _ inferInstance inferInstance
      (hspec _ hW) (hspec _ hQ) _
      (isFirstOrderThickening_specMap _ hπ hπ2) g k hgk)
  refine ⟨{ s.hom with commutes' := fun r => ?_ }, AlgHom.ext fun x => ?_⟩
  · exact congr($(hs₂).hom r)
  · have h1 := congr($(hs₁).hom x)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id,
      RingHom.id_apply] at h1
    exact h1

end Stacks.Smooth

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 061K, the implication (1) ⟹ (2), with condition (2) read on affine opens.** If
`f : X ⟶ Y` is a formally smooth morphism of algebraic spaces over `S`, then in every
commuting square of étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y` over `ψ : U ⟶ V` the scheme
morphism underlying `ψ` is affine-locally formally smooth, that is, satisfies condition (3) of
[Stacks Project, Tag 0D0F].

[Stacks Project, Tag 061H] solves every lifting problem for `ψ` along a first-order thickening
of affine schemes *contained in the site*, and
`Stacks.Smooth.formallySmoothAffineLocally_of_exists_lift_of_size_lt` upgrades that to formal
smoothness of the ring maps on affine opens, since the only thickening it needs is the
spectrum of a polynomial presentation of those sections and the site contains it.

It is weaker than condition (2) of Tag 061K, which asks for the lifting property of `ψ`
against thickenings of arbitrary affine schemes. -/
theorem holdsOnEveryEtaleChart_formallySmoothAffineLocally {f : X ⟶ Y}
    (hf : FormallySmooth f) :
    HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothAffineLocally.{u}) f := by
  intro U V a b h ha hb hsq
  exact Stacks.Smooth.formallySmoothAffineLocally_of_exists_lift_of_size_lt
    B.aleph0_lt_cutoff _ U.left.property V.left.property
    fun T T' hT hT' hTB hT'B i hi g k hcomm =>
      exists_lift_scheme_of_formallySmooth hf ha hb hsq hT hT' hTB hT'B hi hcomm

/-- **Stacks 061K, condition (2) for an affine chart morphism.** Let `f : X ⟶ Y` be a formally
smooth morphism of algebraic spaces over `S` and let `a : U ⟶ X`, `b : V ⟶ Y` be étale scheme
charts fitting in a commuting square over `ψ : U ⟶ V`. If the scheme morphism underlying `ψ`
is affine, then it is formally smooth in the sense of the infinitesimal lifting property
`Stacks.Smooth.FormallySmoothScheme`.

For an affine morphism the implication (3) ⟹ (1) of [Stacks Project, Tag 0D0F] is available —
`Stacks.Smooth.formallySmooth_of_formallySmoothAffineLocally_of_isAffineHom` — because a lift
is then a section of a base change and no gluing of local lifts is needed. This is therefore
the instance of condition (2) of [Stacks Project, Tag 061K] which the library reaches with no
extra hypothesis. -/
theorem formallySmoothScheme_map_of_formallySmooth_of_isAffineHom {f : X ⟶ Y}
    (hf : FormallySmooth f) (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map ψ ≫ b = a ≫ f)
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map ψ)] :
    Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ) :=
  Stacks.Smooth.formallySmoothScheme_of_formallySmooth
    (Stacks.Smooth.formallySmooth_of_formallySmoothAffineLocally_of_isAffineHom _
      (holdsOnEveryEtaleChart_formallySmoothAffineLocally hf U V a b ψ ha hb hsq))

/-- **Stacks 03MJ, condition (1) implies condition (2).** A property of morphisms of schemes
which holds on every commuting square of étale charts of a morphism of algebraic spaces over
`S` holds on one such square whose chart of the source is surjective.

The square is produced from an atlas of the target by
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`, Stacks 02X1, and the
every-chart hypothesis is instantiated at it. No locality hypothesis on the property is
needed; the converse implication is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_surjectiveChart`. -/
theorem holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart
    (P : MorphismProperty Scheme.{u}) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hall : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnSurjectiveEtaleChart B S hS P f := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact ⟨U, V, p, b, α, hpEtale, hbEtale, hpSurj, hcomm.symm,
    hall U V p b α hpEtale hbEtale hcomm.symm⟩

/-- **Stacks 061K, the implication (1) ⟹ (3), with condition (3) read on affine opens.** A
formally smooth morphism of algebraic spaces over `S` admits a commuting square of étale
scheme charts whose chart of the source is surjective and whose underlying scheme morphism is
affine-locally formally smooth. -/
theorem holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : FormallySmooth f) :
    HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothAffineLocally.{u}) f :=
  holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart _ hX hY
    (holdsOnEveryEtaleChart_formallySmoothAffineLocally hf)

/-- **Stacks 061K, the implication (1) ⟹ (2).** If `f : X ⟶ Y` is a formally smooth morphism
of algebraic spaces over `S`, then the scheme morphism in every commuting square of étale
scheme charts of `f` is formally smooth, in the sense of the infinitesimal lifting property
`Stacks.Smooth.FormallySmoothScheme`.

The restriction of `AlgebraicGeometry.Space.FormallySmooth` to thickenings the site contains is
no obstruction, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothAffineLocally`; what that supplies
is formal smoothness of the ring maps on affine opens, and
`Stacks.Smooth.formallySmooth_of_formallySmooth_appLE` — the implication (3) ⟹ (1) of
[Stacks Project, Tag 0D0F] — turns it into the lifting property. The statement does not carry
the tag because the tag asserts the biconditionals, which are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean`. -/
theorem holdsOnEveryEtaleChart_formallySmoothScheme' {f : X ⟶ Y} (hf : FormallySmooth f) :
    HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f :=
  fun U V a b h ha hb hsq =>
    Stacks.Smooth.formallySmooth_of_formallySmooth_appLE _ fun W hW V₀ hV₀ e =>
      (Stacks.Smooth.formallySmoothAffineLocally_iff_appLE _).mp
        (holdsOnEveryEtaleChart_formallySmoothAffineLocally hf U V a b h ha hb hsq)
        ⟨V₀, hV₀⟩ ⟨W, hW⟩ e

/-- `holdsOnEveryEtaleChart_formallySmoothScheme'` in its original signature, whose further
hypotheses it does not need. -/
theorem holdsOnEveryEtaleChart_formallySmoothScheme
    (h0D0F : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'),
      Stacks.Smooth.FormallySmoothAffineLocally g → Stacks.Smooth.FormallySmoothScheme g)
    {f : X ⟶ Y} (hf : FormallySmooth f) :
    HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  clear h0D0F
  exact holdsOnEveryEtaleChart_formallySmoothScheme' hf

/-- **Stacks 061K, the implication (1) ⟹ (3).** A formally smooth morphism of algebraic spaces
over `S` admits a commuting square of étale scheme charts whose chart of the source is
surjective and whose underlying scheme morphism is formally smooth.

The statement does not carry the tag because the tag asserts the biconditionals, which are
proved in `StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean`. -/
theorem holdsOnSurjectiveEtaleChart_formallySmoothScheme'
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : FormallySmooth f) :
    HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f :=
  holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart _ hX hY
    (holdsOnEveryEtaleChart_formallySmoothScheme' hf)

/-- `holdsOnSurjectiveEtaleChart_formallySmoothScheme'` in its original signature, whose further
hypotheses it does not need. -/
theorem holdsOnSurjectiveEtaleChart_formallySmoothScheme
    (h0D0F : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'),
      Stacks.Smooth.FormallySmoothAffineLocally g → Stacks.Smooth.FormallySmoothScheme g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : FormallySmooth f) :
    HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  clear h0D0F
  exact holdsOnSurjectiveEtaleChart_formallySmoothScheme' hX hY hf

end AlgebraicGeometry.Space

end
