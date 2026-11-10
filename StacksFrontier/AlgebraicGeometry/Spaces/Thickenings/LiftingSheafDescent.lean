module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# A lift over an étale atlas descends to a global lift

Let `B`, `X'` and `Y` be algebraic spaces over a scheme `S`, let `X ⊆ X'` be a subspace and let
`a : X ⟶ Y` be a morphism over `B`.  A *lift* of `a` over an étale chart `U'` of `X'` is a
morphism `U' ⟶ Y` over `B` agreeing with `a` on `X ×_{X'} U'`; these are the sections of the
sheaf of lifts `AlgebraicGeometry.Space.liftsSubfunctor` of [Stacks Project, Tag 061D].

This file proves that a lift over a *surjective* étale chart which is invariant under the kernel
pair of that chart comes from exactly one morphism `X' ⟶ Y` which is itself a lift of `a`, i.e.
which lies over `B` and restricts to `a` on `X`.  That is the descent which turns a chartwise
construction of lifts into a global one.

## Main results

* `AlgebraicGeometry.Space.hom_ext_of_isLocallySurjective`: a locally surjective morphism of
  type-valued presheaves can be cancelled on the left against a sheaf.
* `AlgebraicGeometry.Space.isLocallySurjective_fromPreimage`: the preimage of a subfunctor along
  a locally surjective morphism maps locally surjectively onto the subfunctor.
* `AlgebraicGeometry.Space.existsUnique_hom_of_isChartLift_atlas`: **the descent.**  A lift over
  a surjective étale chart which is invariant under the kernel pair of the chart is the
  restriction of exactly one morphism `X' ⟶ Y` lying over `B` and restricting to `a` on `X`.
* `AlgebraicGeometry.Space.existsUnique_hom_of_isChartLift_family`: **the global sections of the
  sheaf of lifts are the global lifts.**  A family of lifts indexed by every étale chart of `X'`
  and compatible with restriction is the family of restrictions of exactly one morphism
  `X' ⟶ Y` lying over `B` and restricting to `a` on `X`.

## Implementation notes

The morphism `X' ⟶ Y` is produced by `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`,
that is by the fact that a surjective étale atlas is a coequalizer of its kernel pair in fppf
sheaves ([Stacks Project, Tag 0262], part (3)).  What has to be checked afterwards is that the
descended morphism is again a lift, and both clauses are checked by cancelling a locally
surjective morphism on the left:

* that it lies over `B` is the equality of two morphisms `X' ⟶ B`, and the atlas itself is
  cancelled, by `AlgebraicGeometry.Space.hom_ext_of_etale_atlas`;
* that it restricts to `a` on `X` is an equality of two morphisms `X ⟶ Y`, and what is cancelled
  is the projection `X ×_{X'} U' ⟶ X`, which is locally surjective because the atlas is
  (`AlgebraicGeometry.Space.isLocallySurjective_of_surjective_etale`) and local surjectivity is
  inherited by the base change along the inclusion of a subfunctor.  The equation it is
  cancelled against is exactly the second clause of
  `AlgebraicGeometry.Space.isChartLift_iff_restrict`, the form of the lifting condition that
  speaks about the fibre product `X ×_{X'} U'`.

No hypothesis on the subspace `X ⊆ X'` is needed, so none is imposed; in the intended
application `X ⊂ X'` is a first order thickening.

Passing from the atlas form to the chart-indexed form uses two closure properties of the étale
charts, both of which hold with no hypothesis on `X'` beyond being a sheaf with an atlas: a
represented kernel pair of a chart is again a chart, which is what turns the compatibility of a
chart-indexed family into the kernel-pair invariance the atlas form asks for; and the fibre
product of an arbitrary chart with the atlas is a chart covering that arbitrary chart, which is
what extends the agreement from the atlas to every chart.  The second is the covering of
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` written out for a single chart,
and the agreement is concluded from separatedness of the restriction of `Y` to the small étale
site, `AlgebraicGeometry.Space.SmallEtale.isSheaf_comp_toOver`.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Cancelling a locally surjective morphism -/

section LocallySurjective

variable {D : Type*} [Category D] {J : GrothendieckTopology D}

/-- **A locally surjective morphism of type-valued presheaves can be cancelled on the left
against a sheaf.**  Two morphisms into a sheaf which agree after a locally surjective morphism
agree on every section locally, hence agree. -/
theorem hom_ext_of_isLocallySurjective {F G H : Dᵒᵖ ⥤ Type u} (π : F ⟶ G)
    (hπ : Presheaf.IsLocallySurjective J π) (hH : Presieve.IsSheaf J H)
    {f g : G ⟶ H} (hfg : π ≫ f = π ≫ g) : f = g := by
  ext U x
  refine (hH _ (hπ.imageSieve_mem x)).isSeparatedFor.ext fun V b hb => ?_
  obtain ⟨y, hy⟩ := hb
  have hres : f.app (op V) (G.map b.op x) = g.app (op V) (G.map b.op x) := by
    rw [← hy]
    exact ConcreteCategory.congr_hom (congr_app hfg (op V)) y
  exact (NatTrans.naturality_apply f b.op x).symm.trans
    (hres.trans (NatTrans.naturality_apply g b.op x))

/-- **The preimage of a subfunctor along a locally surjective morphism maps locally
surjectively onto the subfunctor.**  A section of the subfunctor lifts locally because it lifts
locally in the ambient functor, and every such local lift lies in the preimage. -/
theorem isLocallySurjective_fromPreimage {F F' : Dᵒᵖ ⥤ Type u} (Z : Subfunctor F) (π : F' ⟶ F)
    (hπ : Presheaf.IsLocallySurjective J π) :
    Presheaf.IsLocallySurjective J (Z.fromPreimage π) := by
  refine ⟨fun {U} x => ?_⟩
  refine J.superset_covering ?_ (hπ.imageSieve_mem (x : F.obj (op U)))
  rintro V b ⟨y, hy⟩
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change π.app (op V) y ∈ Z.obj (op V)
  rw [hy]
  exact Z.map b.op x.2

end LocallySurjective

/-! ### Descent of a lift along a surjective étale atlas -/

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {B X' Y : AlgebraicSpaces C S hS}

/-- An étale morphism of the big fppf site followed by a morphism to a presheaf which is étale
after every represented base change has composite with the same property.

This was `AlgebraicGeometry.Space.presheaf_etale_comp` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartCriterion.lean`, where it carried a clause of
Stacks 03EC; that module now keeps only `isEtale_of_presheaf_etale_comp_chart`, and the two
uses below are the only ones left in the library, so it lives here as a private lemma. Stacks
03EC is registered in `StacksFrontier/AlgebraicGeometry/Spaces/EtaleCharts.lean`. -/
private theorem presheaf_etale_comp' {U V : BigFppfOver C S hS}
    {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (δ : U ⟶ V) (g : yoneda.obj V ⟶ Z)
    (hδ : Etale ((BigFppfOver.toScheme C S hS).map δ))
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf g) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (yoneda.map δ ≫ g) :=
  have := isMultiplicative_presheaf_etale C S hS
  MorphismProperty.comp_mem _ _ _
    (presheaf_yoneda_map_of_inverseImage C S hS
      (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})) inferInstance δ hδ) hg

/-- The chart `R' ⟶ W ⟶ X'` obtained by precomposing a chart `W` with an étale morphism. -/
private def chartComp (W : SmallEtale C S hS X'.1) {R' : BigFppfOver C S hS}
    (δ : R' ⟶ W.1.left) (hδ : Etale ((BigFppfOver.toScheme C S hS).map δ)) :
    SmallEtale C S hS X'.1 :=
  ⟨CostructuredArrow.mk (yoneda.map δ ≫ W.1.hom),
    presheaf_etale_comp' C S hS δ W.1.hom hδ W.property⟩

/-- The morphism of charts from `chartComp W δ hδ` to `W` given by `δ`. -/
private def chartCompHom (W : SmallEtale C S hS X'.1) {R' : BigFppfOver C S hS}
    (δ : R' ⟶ W.1.left) (hδ : Etale ((BigFppfOver.toScheme C S hS).map δ)) :
    chartComp C S hS W δ hδ ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk δ rfl)

/-- **A lift over a surjective étale chart which is invariant under the kernel pair of the chart
descends to a unique global lift.**  Let `X ⊆ X'` be a subspace of an algebraic space, let
`a : X ⟶ Y` be a morphism over `B`, and let `U₁` be an étale chart of `X'` whose structure
morphism is surjective.  A lift `α : U₁ ⟶ Y` of `a` whose two restrictions along any represented
kernel pair of the chart agree is `U₁ ⟶ X' ⟶ Y` for exactly one morphism `a' : X' ⟶ Y`, and that
`a'` lies over `B` and restricts to `a` on `X`.

This is the descent that produces a global lift out of a chartwise construction.  The
construction of a lift over an affine chart is not performed here. -/
theorem existsUnique_hom_of_isChartLift_atlas (p : X' ⟶ B) (q : Y ⟶ B)
    {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1) (U₁ : SmallEtale C S hS X'.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS))) U₁.1.hom)
    (α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U₁) ⟶ Y.1)
    (hα : IsChartLift C S hS p q a U₁ α)
    (hinv : ∀ (R' : BigFppfOver C S hS)
      (s t : R' ⟶ (SmallEtale.toOver C S hS X'.1).obj U₁),
      IsPullback (yoneda.map s) (yoneda.map t) U₁.1.hom U₁.1.hom →
        yoneda.map s ≫ α = yoneda.map t ≫ α) :
    ∃! a' : X'.1 ⟶ Y.1,
      U₁.1.hom ≫ a' = α ∧ a' ≫ q.hom = p.hom ∧ X.ι ≫ a' = a := by
  have hX' : Presheaf.IsSheaf (BigFppfOver.topology C S hS) X'.1 := X'.2.isSheaf
  have hY : Presheaf.IsSheaf (BigFppfOver.topology C S hS) Y.1 := Y.2.isSheaf
  have hB : Presheaf.IsSheaf (BigFppfOver.topology C S hS) B.1 := B.2.isSheaf
  obtain ⟨d, hd, hdu⟩ := existsUnique_hom_of_atlas_invariant C S hS hX' hY U₁.1.hom hsurj U₁.2 α
    hinv
  refine ⟨d, ⟨hd, ?_, ?_⟩, fun y hy => hdu y hy.1⟩
  · refine hom_ext_of_etale_atlas C S hS hX' hB U₁.1.hom hsurj U₁.2 ?_
    rw [← Category.assoc, hd, hα.1]
  · have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        (X.fromPreimage U₁.1.hom) :=
      isLocallySurjective_fromPreimage X U₁.1.hom
        (isLocallySurjective_of_surjective_etale C S hS U₁.1.hom hsurj U₁.2)
    refine hom_ext_of_isLocallySurjective (X.fromPreimage U₁.1.hom) hloc
      ((isSheaf_iff_isSheaf_of_type _ _).1 hY) ?_
    rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, hd]
    exact ((isChartLift_iff_restrict C S hS p q a U₁ α).1 hα).2

/-! ### Descent of a family of lifts indexed by every chart -/

/-- **A family of lifts indexed by every étale chart of `X'`, compatible with restriction, comes
from exactly one global lift.**  Let `X ⊆ X'` be a subspace of an algebraic space and let
`a : X ⟶ Y` be a morphism over `B`.  A rule assigning to every étale chart `W` of `X'` a lift
`α W : W ⟶ Y` of `a`, compatibly with the morphisms of charts — that is, a global section of the
sheaf of lifts of [Stacks Project, Tag 061D] — is the family of restrictions of exactly one
morphism `a' : X' ⟶ Y`, and that `a'` lies over `B` and restricts to `a` on `X`.

This is the identification of the global lifts with the global sections of the sheaf of lifts.
The morphism is produced from the restriction of the family to a surjective étale chart by
`existsUnique_hom_of_isChartLift_atlas`; the kernel pair of that chart is itself a chart, which
is what turns the compatibility of the family into the invariance that theorem asks for, and an
arbitrary chart `W` is compared with the atlas over the fibre product of the two, which covers
`W` because the atlas is surjective. -/
theorem existsUnique_hom_of_isChartLift_family (p : X' ⟶ B) (q : Y ⟶ B)
    {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1)
    (α : ∀ W : SmallEtale C S hS X'.1,
      yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj W) ⟶ Y.1)
    (hα : ∀ W, IsChartLift C S hS p q a W (α W))
    (hcompat : ∀ {W V : SmallEtale C S hS X'.1} (m : V ⟶ W),
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α W = α V) :
    ∃! a' : X'.1 ⟶ Y.1,
      (∀ W, W.1.hom ≫ a' = α W) ∧ a' ≫ q.hom = p.hom ∧ X.ι ≫ a' = a := by
  obtain ⟨U₀, b, hsurj, hetale⟩ := X'.2.exists_atlas
  set U₁ : SmallEtale C S hS X'.1 := ⟨CostructuredArrow.mk b, hetale⟩
  -- The kernel pair of the atlas is itself a chart, so the family is invariant under it.
  have hinv : ∀ (R' : BigFppfOver C S hS)
      (s t : R' ⟶ (SmallEtale.toOver C S hS X'.1).obj U₁),
      IsPullback (yoneda.map s) (yoneda.map t) U₁.1.hom U₁.1.hom →
        yoneda.map s ≫ α U₁ = yoneda.map t ≫ α U₁ := by
    intro R' s t hR
    have hsEtale : Etale ((BigFppfOver.toScheme C S hS).map s) :=
      hetale.property b (yoneda.map t) s hR.flip
    exact (hcompat (chartCompHom C S hS U₁ s hsEtale)).trans
      (hcompat (ObjectProperty.homMk (CostructuredArrow.homMk t hR.w.symm) :
        chartComp C S hS U₁ s hsEtale ⟶ U₁)).symm
  obtain ⟨a', ⟨hatlas, hq, hres⟩, huniq⟩ :=
    existsUnique_hom_of_isChartLift_atlas C S hS p q a U₁ hsurj (α U₁) (hα U₁) hinv
  -- The descended morphism restricts to the given lift on every chart, not only on the atlas.
  have hsheaf : Presheaf.IsSheaf (SmallEtale.topology C S hS X'.1)
      ((SmallEtale.toOver C S hS X'.1).op ⋙ Y.1) :=
    SmallEtale.isSheaf_comp_toOver C S hS X'.1 Y.2.isSheaf
  have hall : ∀ W : SmallEtale C S hS X'.1, W.1.hom ≫ a' = α W := by
    intro W
    have hrep : yoneda.relativelyRepresentable U₁.1.hom := U₁.property.rep
    set g := W.1.hom
    set pr : hrep.pullback g ⟶ U₁.1.left := hrep.fst' g with hpr
    set pq : hrep.pullback g ⟶ W.1.left := hrep.snd g
    have hw : yoneda.map pr ≫ U₁.1.hom = yoneda.map pq ≫ g := by
      rw [hpr, Functor.relativelyRepresentable.map_fst']
      exact hrep.w g
    have hqEtale : Etale ((BigFppfOver.toScheme C S hS).map pq) :=
      U₁.property.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g)
    have hqSurj : Surjective ((BigFppfOver.toScheme C S hS).map pq) :=
      hsurj.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g)
    set Vc := chartComp C S hS W pq hqEtale
    set mW : Vc ⟶ W := chartCompHom C S hS W pq hqEtale
    set mU : Vc ⟶ U₁ := ObjectProperty.homMk (CostructuredArrow.homMk pr hw)
    have hcov : Sieve.generate (Presieve.singleton mW) ∈
        SmallEtale.topology C S hS X'.1 W := by
      refine Precoverage.generate_mem_toGrothendieck ?_
      rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
      exact C.singleton_mem_etalePrecoverage _ hqSurj hqEtale
    have hwW : yoneda.map ((SmallEtale.toOver C S hS X'.1).map mW) ≫ W.1.hom = Vc.1.hom :=
      CostructuredArrow.w _
    have hwU : yoneda.map ((SmallEtale.toOver C S hS X'.1).map mU) ≫ U₁.1.hom = Vc.1.hom :=
      CostructuredArrow.w _
    -- the two sections of the restricted sheaf agree after restriction along the covering
    have hagree : yoneda.map ((SmallEtale.toOver C S hS X'.1).map mW) ≫ (W.1.hom ≫ a') =
        yoneda.map ((SmallEtale.toOver C S hS X'.1).map mW) ≫ α W := by
      rw [hcompat mW, ← Category.assoc, hwW, ← hwU, Category.assoc, hatlas, hcompat mU]
    have key : yonedaEquiv (W.1.hom ≫ a') = yonedaEquiv (α W) := by
      refine ((isSheaf_iff_isSheaf_of_type _ _).1 hsheaf _ hcov).isSeparatedFor.ext ?_
      rintro Z f ⟨T, h, k, hk, rfl⟩
      cases hk
      have hcomp :
          yoneda.map ((SmallEtale.toOver C S hS X'.1).map (h ≫ mW)) ≫ (W.1.hom ≫ a') =
            yoneda.map ((SmallEtale.toOver C S hS X'.1).map (h ≫ mW)) ≫ α W := by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hagree]
      exact (yonedaEquiv_naturality _ _).trans
        ((congrArg yonedaEquiv hcomp).trans (yonedaEquiv_naturality _ _).symm)
    exact yonedaEquiv.injective key
  refine ⟨a', ⟨hall, hq, hres⟩, fun y hy => huniq y ⟨hy.1 U₁, hy.2⟩⟩

end AlgebraicGeometry.Space

end
