module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.EtaleNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationFiniteness

/-!
# The étale-local decomposition of the normalization of a divisor

Let `D` be a closed subscheme of a locally Noetherian scheme `X` whose normalization
`ν : D^ν ⟶ D` is unramified. Tag 04HJ, applied to the finite unramified morphism `D^ν ⟶ X`,
produces around any point `p` of `X` an étale chart `f : U ⟶ X` on which the base change
`D^ν ×_X U` splits into finitely many pairwise disjoint opens, each closed in `U`.

This file repackages that statement so that the base change is replaced by the normalization of
the pullback divisor `D.comap f`: because normalization commutes with étale base change, the two
are canonically identified, and the identification is recorded here as a pullback square and as
an isomorphism with the fibre product. The resulting decomposition is stated in the shape the
fibre-power decomposition machinery consumes, with each piece presented both as an open
subscheme of the normalization and as the closed subscheme of the chart that it cuts out.

## Main definitions

* `Stacks.Divisors.divisorChartPreimageOpensIso` restricts an isomorphism of schemes to an
  isomorphism from the preimage of an open subscheme onto that open subscheme.
* `Stacks.Divisors.divisorNormalizationComapPullbackIso` identifies the normalization of the
  pullback divisor with the fibre product of `D^ν ⟶ X` and the chart.

## Main results

* `Stacks.Divisors.isPullback_divisorNormalizationToAmbient_comap`: the square formed by the two
  morphisms to the ambient schemes, the chart, and the morphism of normalizations is cartesian.
* `Stacks.Divisors.exists_openImmersion_closedCover_divisorNormalization_comap` transports a
  decomposition of the base change `D^ν ×_X U` to one of the normalization of `D.comap f`.
* `Stacks.Divisors.exists_etaleChart_closedCover_divisorNormalization` is the étale-local
  statement: around every point of `X` there is an étale chart on which the normalization of the
  pullback divisor is a finite disjoint union of open subschemes, each mapping to the chart by a
  closed immersion and canonically identified with the closed subscheme it cuts out.

## Implementation notes

The cartesian square is obtained by pasting the cartesian square of normalizations onto the
cartesian square of divisor subschemes; both factor through the subscheme cut out by the divisor,
so the horizontal pasting lemma applies after a flip.

Each piece of the decomposition is the preimage of the corresponding open of the base change
under that identification. The restriction of an isomorphism to an open and its full preimage is
an isomorphism, which is used both to see that the piece is closed in the chart and to transport
the covering and disjointness statements.

The identification of a piece with the closed subscheme of the chart it cuts out is the
scheme-theoretic image: for a closed immersion the canonical morphism to the image is an
isomorphism, and it composes with the embedding of the image to give back the closed immersion.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 04HJ](https://stacks.math.columbia.edu/tag/04HJ)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Function

universe u

namespace Stacks.Divisors

/-- The restriction of an isomorphism of schemes to an open subscheme of the target and its full
preimage is an isomorphism. -/
public noncomputable def divisorChartPreimageOpensIso {Y Z : Scheme.{u}} (G : Y ≅ Z)
    (W : Z.Opens) : (G.hom ⁻¹ᵁ W).toScheme ≅ W.toScheme :=
  asIso (G.hom ∣_ W)

/-- The restricted isomorphism is compatible with the two open immersions and the original
isomorphism. -/
public theorem divisorChartPreimageOpensIso_hom_ι {Y Z : Scheme.{u}} (G : Y ≅ Z) (W : Z.Opens) :
    (divisorChartPreimageOpensIso G W).hom ≫ W.ι = (G.hom ⁻¹ᵁ W).ι ≫ G.hom :=
  morphismRestrict_ι _ _

/-- The range of the base map of the open immersion of an open subscheme is that open set. -/
public theorem divisorChartOpensRangeBase {Y : Scheme.{u}} (W : Y.Opens) :
    Set.range W.ι.base = (W : Set Y) :=
  W.range_ι

variable {X U : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (f : U ⟶ X) [Etale f] (D : X.IdealSheafData)

/-- **The morphism to the ambient scheme is stable under étale localization of the divisor.**
The square formed by `D^ν ⟶ X`, the chart `f : U ⟶ X`, the morphism to the ambient scheme of the
pullback divisor, and the induced morphism of normalizations is cartesian. It is the horizontal
pasting of the cartesian square of normalizations with the cartesian square of the divisor
subschemes. -/
public theorem isPullback_divisorNormalizationToAmbient_comap :
    IsPullback (divisorNormalizationToAmbient (D.comap f)) (comapNormalizationMap f D) f
      (divisorNormalizationToAmbient D) :=
  (isPullback_comapNormalizationMap f D).flip.paste_horiz (isPullback_comapSubschemeMap f D)

/-- The normalization of the pullback of `D` along an étale chart is the fibre product of
`D^ν ⟶ X` with the chart. -/
public noncomputable def divisorNormalizationComapPullbackIso :
    divisorNormalizationScheme (D.comap f) ≅ pullback (divisorNormalizationToAmbient D) f :=
  (isPullback_divisorNormalizationToAmbient_comap f D).flip.isoPullback

/-- The identification of the normalization of the pullback divisor with the fibre product is
compatible with the morphism of normalizations. -/
public theorem divisorNormalizationComapPullbackIso_hom_fst :
    (divisorNormalizationComapPullbackIso f D).hom ≫
        pullback.fst (divisorNormalizationToAmbient D) f = comapNormalizationMap f D :=
  IsPullback.isoPullback_hom_fst _

/-- The identification of the normalization of the pullback divisor with the fibre product is
compatible with the morphisms to the chart. -/
public theorem divisorNormalizationComapPullbackIso_hom_snd :
    (divisorNormalizationComapPullbackIso f D).hom ≫
        pullback.snd (divisorNormalizationToAmbient D) f =
      divisorNormalizationToAmbient (D.comap f) :=
  IsPullback.isoPullback_hom_snd _

/-- A decomposition of the base change `D^ν ×_X U` into pairwise disjoint opens which are closed
in the chart transports to a decomposition of the normalization of the pullback divisor: the
pieces are the preimages of the given opens under the identification of the normalization of
`D.comap f` with the fibre product, and each is canonically identified with the closed subscheme
of the chart that it cuts out. -/
public theorem exists_openImmersion_closedCover_divisorNormalization_comap (n : ℕ)
    (V : Fin n → (pullback (divisorNormalizationToAmbient D) f).Opens)
    (hcover : sSup (Set.range V) = ⊤) (hdisj : Pairwise (Disjoint on V))
    (hclosed : ∀ j, IsClosedImmersion
      ((V j).ι ≫ pullback.snd (divisorNormalizationToAmbient D) f)) :
    ∃ (A : Fin n → Scheme.{u}) (ε : ∀ j, A j ⟶ divisorNormalizationScheme (D.comap f)),
      (∀ j, IsOpenImmersion (ε j)) ∧
      (∀ j, IsClosedImmersion (ε j ≫ divisorNormalizationToAmbient (D.comap f))) ∧
      (∀ y : divisorNormalizationScheme (D.comap f), ∃ j, y ∈ Set.range (ε j).base) ∧
      (∀ j k, j ≠ k → Disjoint (Set.range (ε j).base) (Set.range (ε k).base)) ∧
      (∀ j, ∃ e : A j ≅ ((ε j ≫ divisorNormalizationToAmbient (D.comap f)).ker).subscheme,
        e.hom ≫ ((ε j ≫ divisorNormalizationToAmbient (D.comap f)).ker).subschemeι =
          ε j ≫ divisorNormalizationToAmbient (D.comap f)) := by
  set G := divisorNormalizationComapPullbackIso f D with hGdef
  have hGsnd : G.hom ≫ pullback.snd (divisorNormalizationToAmbient D) f =
      divisorNormalizationToAmbient (D.comap f) := by
    rw [hGdef]; exact divisorNormalizationComapPullbackIso_hom_snd f D
  -- Each piece, read through the identification, is an isomorphism onto the given open.
  have key : ∀ j, (G.hom ⁻¹ᵁ V j).ι ≫ divisorNormalizationToAmbient (D.comap f) =
      (divisorChartPreimageOpensIso G (V j)).hom ≫
        ((V j).ι ≫ pullback.snd (divisorNormalizationToAmbient D) f) := by
    intro j
    calc (G.hom ⁻¹ᵁ V j).ι ≫ divisorNormalizationToAmbient (D.comap f)
        = (G.hom ⁻¹ᵁ V j).ι ≫ G.hom ≫ pullback.snd _ _ := by rw [hGsnd]
      _ = ((G.hom ⁻¹ᵁ V j).ι ≫ G.hom) ≫ pullback.snd _ _ := (Category.assoc _ _ _).symm
      _ = ((divisorChartPreimageOpensIso G (V j)).hom ≫ (V j).ι) ≫ pullback.snd _ _ := by
          rw [divisorChartPreimageOpensIso_hom_ι]
      _ = (divisorChartPreimageOpensIso G (V j)).hom ≫
            (V j).ι ≫ pullback.snd _ _ := Category.assoc _ _ _
  have hCI : ∀ j, IsClosedImmersion
      ((G.hom ⁻¹ᵁ V j).ι ≫ divisorNormalizationToAmbient (D.comap f)) := by
    intro j
    rw [key j]
    have := hclosed j
    infer_instance
  refine ⟨fun j => (G.hom ⁻¹ᵁ V j).toScheme, fun j => (G.hom ⁻¹ᵁ V j).ι,
    fun j => inferInstance, hCI, ?_, ?_, ?_⟩
  · intro y
    have hy : G.hom.base y ∈ sSup (Set.range V) := by
      rw [hcover]; exact TopologicalSpace.Opens.mem_top _
    obtain ⟨W, ⟨j, rfl⟩, hW⟩ := TopologicalSpace.Opens.mem_sSup.mp hy
    exact ⟨j, ⟨y, hW⟩, rfl⟩
  · intro j k hjk
    rw [divisorChartOpensRangeBase, divisorChartOpensRangeBase]
    exact Set.disjoint_left.mpr fun z hz hz' =>
      Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj hjk)) hz hz'
  · intro j
    have := hCI j
    exact ⟨asIso ((G.hom ⁻¹ᵁ V j).ι ≫ divisorNormalizationToAmbient (D.comap f)).toImage,
      Scheme.Hom.toImage_imageι _⟩

end Stacks.Divisors

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)

/-- **Étale-local structure of the normalization of a divisor.** Around every point of the
ambient scheme there is an étale chart on which the normalization of the pullback divisor is a
finite disjoint union of open subschemes, each mapping to the chart by a closed immersion. -/
public theorem exists_etaleChart_closedCover_divisorNormalization
    [Unramified (divisorNormalization D)] (p : X) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (hU : IsLocallyNoetherian U) (hf : Etale f) (u : U),
      f.base u = p ∧
      ∃ (m : ℕ) (A : Fin m → Scheme.{u})
        (ε : ∀ j, A j ⟶ @divisorNormalizationScheme U hU (D.comap f)),
        (∀ j, IsOpenImmersion (ε j)) ∧
        (∀ j, IsClosedImmersion
          (ε j ≫ @divisorNormalizationToAmbient U hU (D.comap f))) ∧
        (∀ y : @divisorNormalizationScheme U hU (D.comap f), ∃ j, y ∈ Set.range (ε j).base) ∧
        (∀ j k, j ≠ k → Disjoint (Set.range (ε j).base) (Set.range (ε k).base)) ∧
        (∀ j, ∃ e : A j ≅ ((ε j ≫ @divisorNormalizationToAmbient U hU (D.comap f)).ker).subscheme,
            e.hom ≫ ((ε j ≫ @divisorNormalizationToAmbient U hU (D.comap f)).ker).subschemeι =
              ε j ≫ @divisorNormalizationToAmbient U hU (D.comap f)) := by
  obtain ⟨U₀, n, V, hcover, hdisj, hclosed⟩ :=
    exists_etaleNeighborhood_disjoint_closed_decomposition_divisorNormalization D p
  have hUN : IsLocallyNoetherian U₀.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian U₀.toBase
  obtain ⟨A, ε, hopen, hclosed', hcov, hdis, hker⟩ :=
    exists_openImmersion_closedCover_divisorNormalization_comap U₀.toBase D n V hcover hdisj
      hclosed
  exact ⟨U₀.scheme, U₀.toBase, hUN, inferInstance, U₀.point, U₀.map_point, n, A, ε, hopen,
    hclosed', hcov, hdis, hker⟩

end Stacks.Divisors

end
