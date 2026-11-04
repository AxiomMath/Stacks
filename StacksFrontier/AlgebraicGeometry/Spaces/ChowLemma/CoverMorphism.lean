module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DenseOpenAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.UnionPreimageCover

/-!
# The morphism `X' ⟶ X` of Stacks 089J

Everything the gluing step of Stacks 089J needs is now available, and this file carries the
step out. The data is: an étale chart `c : W ⟶ X` of an algebraic space over `S`, an open
immersion `j : W ⟶ Y` of the chart into a compactification, and an object `V` of the site
identified with the complement of the diagonals in the `(d)`-fold self-product of the chart over
`X`. Out of it one forms

* the morphism `V ⟶ Y ×_S ⋯ ×_S Y` into the `d`-fold fibre power over the base,
* its scheme-theoretic image `Z`, in which `V` sits as a quasi-compact dense open by Stacks
  01RG, through
  `AlgebraicGeometry.Space.SpacesEtale.isImmersion_diagonalComplementToOverProdObj`,
* the `d` projections `gᵢ : Z ⟶ Y`, and `X' = ⋃ᵢ gᵢ⁻¹(W)`,

and the `d` morphisms `gᵢ⁻¹(W) ⟶ W ⟶ X` glue, because they agree on `V`, to a single
`X' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.chowToOverProd`: the morphism `V ⟶ Y ×_S ⋯ ×_S Y`.
* `AlgebraicGeometry.Space.chowImageObj`: its scheme-theoretic image `Z`, as an object of the
  big fppf category over `S`.
* `AlgebraicGeometry.Space.chowProj`: the `d` projections `gᵢ : Z ⟶ Y`.
* `AlgebraicGeometry.Space.chartOpensRange`: the open `W ⊆ Y`.
* `AlgebraicGeometry.Space.chowCoverObj`: **`X' = ⋃ᵢ gᵢ⁻¹(W)`.**
* `AlgebraicGeometry.Space.chowDenseLift`: the factorization of `V ⟶ Z` through the `i`-th
  member `gᵢ⁻¹(W)` of the covering of `X'`.

## Main results

* `AlgebraicGeometry.Space.chowProj_comp_hom`: each projection of `Z` is a morphism over the
  base.
* `AlgebraicGeometry.Space.toSchemeImageObj_comp_chowProj`: the composite of `V ⟶ Z` with the
  `i`-th projection is the `i`-th projection of the complement of the diagonals followed by the
  open immersion of the chart into the compactification.
* `AlgebraicGeometry.Space.exists_chowCoverHom`: **the morphism `X' ⟶ X` of Stacks 089J exists
  and is unique** for its prescribed restrictions to the `d` members of the covering, and those
  restrictions restrict on `V` to the projections of the complement of the diagonals.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
Stacks 01RG is carried by `AlgebraicGeometry.isOpenImmersion_toImage`, Stacks 084N by
`AlgebraicGeometry.Space.eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top`, and the gluing
itself by
`AlgebraicGeometry.Space.existsUnique_glueHom_unionPreimageObj_of_eq_on_dominant`.

What is **not** proved is that the glued morphism is proper and surjective, which is the rest of
the proof of Stacks 089J. Properness is the valuative-criterion claim, for which the distinctness
statement `AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne` is one
input and `AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat` another;
surjectivity holds only over the open where the fibre degree is minimal, and the general case
needs the induction on the fibre degree. Neither is here.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism from the complement of the diagonals into the `(n+1)`-fold fibre power of the
compactification over the base.** All the factors are the same object `Y` of the site and all the
morphisms from the chart are the same `j : W ⟶ Y`, as in Stacks 089J. -/
def chowToOverProd (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj) :
    V ⟶ overProdObj B S hS (fun _ : Fin (n + 1) ↦ Yo) :=
  SpacesEtale.diagonalComplementToOverProdObj B S hS X Wch c hc hsep (n + 1) V e
    (fun _ ↦ Yo) fun _ ↦ j

variable (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)

/-- **The scheme-theoretic image `Z` of `AlgebraicGeometry.Space.chowToOverProd`**, as an object
of the big fppf category over `S`. -/
def chowImageObj : BigFppfOver B S hS :=
  schemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)

/-- The `i`-th projection `gᵢ : Z ⟶ Y` of the scheme-theoretic image. -/
def chowProj (i : Fin (n + 1)) :
    (chowImageObj B S hS X Wch c hc hsep Yo j n V e).left.obj ⟶
      (BigFppfOver.toScheme B S hS).obj Yo :=
  ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι ≫
    (BigFppfOver.toScheme B S hS).map (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i)

/-- Unfolding lemma for `AlgebraicGeometry.Space.chowProj`: the `i`-th projection is the
inclusion of the scheme-theoretic image followed by the `i`-th projection of the fibre power. -/
theorem chowProj_eq (i : Fin (n + 1)) :
    chowProj B S hS X Wch c hc hsep Yo j n V e i =
      ((BigFppfOver.toScheme B S hS).map
          (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι ≫
        (BigFppfOver.toScheme B S hS).map
          (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i) :=
  rfl

/-- A morphism of the big fppf category over `S` commutes with the structure morphisms, read on
underlying schemes. -/
private theorem toScheme_map_comp_hom {A D : BigFppfOver B S hS} (k : A ⟶ D) :
    (BigFppfOver.toScheme B S hS).map k ≫ B.inclusion.map D.hom = B.inclusion.map A.hom := by
  rw [show (BigFppfOver.toScheme B S hS).map k = B.inclusion.map k.left from rfl,
    ← Functor.map_comp, Over.w]

/-- **Each projection of the scheme-theoretic image is a morphism over the base.** -/
theorem chowProj_comp_hom (i : Fin (n + 1)) :
    chowProj B S hS X Wch c hc hsep Yo j n V e i ≫ B.inclusion.map Yo.hom =
      B.inclusion.map (chowImageObj B S hS X Wch c hc hsep Yo j n V e).hom := by
  have hw := toScheme_map_comp_hom B S hS (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i)
  have key : ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι ≫
        (BigFppfOver.toScheme B S hS).map
          (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i) ≫ B.inclusion.map Yo.hom =
      B.inclusion.map (schemeImageObj B S hS
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).hom := by
    rw [hw]
    exact (schemeImageObj_hom B S hS _).symm
  exact (Category.assoc _ _ _).trans key

/-- **The composite of `V ⟶ Z` with the `i`-th projection is the `i`-th projection of the
complement of the diagonals followed by the open immersion of the chart.** -/
theorem toSchemeImageObj_comp_chowProj (i : Fin (n + 1)) :
    (BigFppfOver.toScheme B S hS).map
        (toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)) ≫
      chowProj B S hS X Wch c hc hsep Yo j n V e i =
    (BigFppfOver.toScheme B S hS).map
        (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i) ≫
      (BigFppfOver.toScheme B S hS).map j := by
  have h1 : (BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e) ≫
      (BigFppfOver.toScheme B S hS).map
        (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i) =
      (BigFppfOver.toScheme B S hS).map
        (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i) ≫
      (BigFppfOver.toScheme B S hS).map j := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (BigFppfOver.toScheme B S hS).map
      (SpacesEtale.diagonalComplementToOverProdObj_comp_π B S hS X Wch c hc hsep (n + 1) V e
        (fun _ ↦ Yo) (fun _ ↦ j) i)
  have h2 : ((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).toImage ≫
      (((BigFppfOver.toScheme B S hS).map
          (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι ≫
        (BigFppfOver.toScheme B S hS).map
          (overProdObjπ B S hS (fun _ : Fin (n + 1) ↦ Yo) i)) =
      (BigFppfOver.toScheme B S hS).map
        (SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i) ≫
      (BigFppfOver.toScheme B S hS).map j := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, h1]
  exact h2

/-! ### The open `W ⊆ Y` and the members of the covering of `X'` -/

/-- **The image of an open immersion of the big fppf category over `S`, as an open of the
underlying scheme of its target.** This is the open `W ⊆ Y` of Stacks 089J. -/
def chartOpensRange {A D : BigFppfOver B S hS} (k : A ⟶ D)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map k)) :
    ((BigFppfOver.toScheme B S hS).obj D).Opens :=
  have := hk
  ((BigFppfOver.toScheme B S hS).map k).opensRange

/-- **A morphism whose composite with a morphism to the ambient scheme factors through an open
immersion has range inside the preimage of its image.** -/
theorem range_subset_preimage_chartOpensRange {A D : BigFppfOver B S hS} (k : A ⟶ D)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map k))
    {T A' : Scheme.{u}} (gg : T ⟶ (BigFppfOver.toScheme B S hS).obj D) (a : A' ⟶ T)
    (b : A' ⟶ (BigFppfOver.toScheme B S hS).obj A)
    (h : a ≫ gg = b ≫ (BigFppfOver.toScheme B S hS).map k) :
    Set.range ⇑a ⊆ (gg ⁻¹ᵁ chartOpensRange B S hS k hk : Set T) := by
  have := hk
  rw [Set.range_subset_iff]
  intro y
  show gg.base (a.base y) ∈ chartOpensRange B S hS k hk
  refine ⟨b.base y, ?_⟩
  have hy := congrArg (fun f : A' ⟶ (BigFppfOver.toScheme B S hS).obj D ↦ f.base y) h
  simpa using hy.symm

/-- **The restriction of a morphism to the preimage of the image of an open immersion has range
inside that image.** -/
theorem range_ι_comp_subset_chartOpensRange {A D : BigFppfOver B S hS} (k : A ⟶ D)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map k))
    {T : Scheme.{u}} (gg : T ⟶ (BigFppfOver.toScheme B S hS).obj D) :
    Set.range ⇑((gg ⁻¹ᵁ chartOpensRange B S hS k hk).ι ≫ gg) ⊆
      Set.range ⇑((BigFppfOver.toScheme B S hS).map k) := by
  have := hk
  rw [Set.range_subset_iff]
  intro x
  have hx : gg.base (((gg ⁻¹ᵁ chartOpensRange B S hS k hk).ι).base x) ∈
      chartOpensRange B S hS k hk := x.2
  exact hx

variable (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **`X'` of Stacks 089J: the union `⋃ᵢ gᵢ⁻¹(W)` of the preimages of the chart inside the
scheme-theoretic image.** -/
def chowCoverObj : BigFppfOver B S hS :=
  unionPreimageObj B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj)

/-- **The lift of `V ⟶ Z` into the `i`-th member `gᵢ⁻¹(W)` of the covering of `X'`.** -/
def chowDenseLift (i : Fin (n + 1)) :
    V ⟶ preimageObj B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) i :=
  openSubObjLift B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ chartOpensRange B S hS j hj)
    (toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))
    (range_subset_preimage_chartOpensRange B S hS j hj _ _ _
      (toSchemeImageObj_comp_chowProj B S hS X Wch c hc hsep Yo j n V e i))

/-- The lift `AlgebraicGeometry.Space.chowDenseLift` followed by the inclusion of `gᵢ⁻¹(W)` into
`Z` is the morphism `V ⟶ Z` into the scheme-theoretic image. -/
theorem chowDenseLift_comp_preimageObjι (i : Fin (n + 1)) :
    chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫
        preimageObjι B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
          (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) i =
      toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e) :=
  openSubObjLift_comp_openSubHom B S hS _ _ _ _

/-! ### The glued morphism -/

/-- **The morphism `X' ⟶ X` of Stacks 089J exists and is unique.**

The data is the one of Stacks 089J: an étale chart `c : W ⟶ X` which is separated as a morphism,
an open immersion `j : W ⟶ Y` of the chart into a compactification, and an object `V` of the
site identified with the complement of the diagonals in the `(n+1)`-fold self-product of the
chart over `X`, whose underlying scheme is compact. The ambient algebraic space is separated
over the base, which is the hypothesis `hq`.

The conclusion says that each member `gᵢ⁻¹(W)` of the covering of `X'` carries a morphism `ρ i`
to the chart which restricts on `V` to the `i`-th projection of the complement of the diagonals,
and that there is exactly one morphism `X' ⟶ X` restricting on the `i`-th member to `ρ i`
followed by the chart.

Separatedness of `X` over the base is used twice: through
`AlgebraicGeometry.Space.SpacesEtale.isImmersion_diagonalComplementToOverProdObj` to know that
`V ⟶ Y ×_S ⋯ ×_S Y` is an immersion, so that Stacks 01RG makes `V` an open of its
scheme-theoretic image; and through Stacks 084N to know that two morphisms to `X` agreeing on a
scheme-theoretically dense open agree. -/
theorem exists_chowCoverHom (q : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hq : IsSeparated B S hS q)
    (hVqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) :
    ∃ ρ : ∀ i : Fin (n + 1), preimageObj B S hS
        (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e)
        (chartOpensRange B S hS j hj) i ⟶ Wch,
      (∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
          SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i) ∧
        ∃! ψ : (yoneda.obj (chowCoverObj B S hS X Wch c hc hsep Yo j n V e hj) :
            (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X.obj,
          ∀ i, yoneda.map (unionPreimageIncl B S hS
              (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
              (chowProj B S hS X Wch c hc hsep Yo j n V e)
              (chartOpensRange B S hS j hj) i) ≫ ψ = yoneda.map (ρ i) ≫ c := by
  have hjoi := hj
  -- the chart is an immersion into the compactification
  have hjimm : ∀ _ : Fin (n + 1), _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map j) := fun _ ↦ inferInstance
  -- separatedness of `X` over the base, read as separatedness of its morphism to the terminal
  -- presheaf
  have hXsep : IsSeparated B S hS
      ((isTerminal_yoneda_obj_base B S hS).from X.obj) := by
    rw [show (isTerminal_yoneda_obj_base B S hS).from X.obj = q from
      (isTerminal_yoneda_obj_base B S hS).hom_ext _ _]
    exact hq
  have himm := SpacesEtale.isImmersion_diagonalComplementToOverProdObj B S hS X Wch c hc hsep
    (isTerminal_yoneda_obj_base B S hS) hXsep n V e (fun _ ↦ Yo) (fun _ ↦ j) hjimm
  have hvo := isOpenImmersion_toSchemeImageObj B S hS
    (chowToOverProd B S hS X Wch c hc hsep Yo j n V e) himm (Or.inl hVqc)
  have hvq : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) := by
    rw [toSchemeImageObj_toScheme]
    have h0 : AlgebraicGeometry.QuasiCompact
        (((BigFppfOver.toScheme B S hS).map
            (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).toImage ≫
          ((BigFppfOver.toScheme B S hS).map
            (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι) := by
      rw [Scheme.Hom.toImage_imageι]
      exact hVqc
    have := h0
    exact QuasiCompact.of_comp
      (((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).toImage)
      (((BigFppfOver.toScheme B S hS).map
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)).imageι)
  have hvdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map
      (toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e))) := by
    rw [toSchemeImageObj_toScheme]
    exact @Scheme.Hom.isSchemeTheoreticallyDominant_toImage _ _ _ hVqc
  -- the restriction of the `i`-th projection to `gᵢ⁻¹(W)`, as a morphism to the chart
  have hjw := toScheme_map_comp_hom B S hS j
  have hrho : ∀ i : Fin (n + 1), ∃ ρ : preimageObj B S hS
      (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
      (chowProj B S hS X Wch c hc hsep Yo j n V e)
      (chartOpensRange B S hS j hj) i ⟶ Wch,
      (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map j =
        (chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ
            chartOpensRange B S hS j hj).ι ≫
          chowProj B S hS X Wch c hc hsep Yo j n V e i := by
    intro i
    have hfac := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac
      ((BigFppfOver.toScheme B S hS).map j)
      ((chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ
          chartOpensRange B S hS j hj).ι ≫
        chowProj B S hS X Wch c hc hsep Yo j n V e i)
      (range_ι_comp_subset_chartOpensRange B S hS j hj
        (chowProj B S hS X Wch c hc hsep Yo j n V e i))
    have hstruct : _root_.AlgebraicGeometry.IsOpenImmersion.lift
        ((BigFppfOver.toScheme B S hS).map j)
        ((chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ
            chartOpensRange B S hS j hj).ι ≫
          chowProj B S hS X Wch c hc hsep Yo j n V e i)
        (range_ι_comp_subset_chartOpensRange B S hS j hj
          (chowProj B S hS X Wch c hc hsep Yo j n V e i)) ≫
        B.inclusion.map Wch.hom =
      B.inclusion.map (preimageObj B S hS
        (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e)
        (chartOpensRange B S hS j hj) i).hom := by
      rw [← hjw, ← Category.assoc, hfac, Category.assoc,
        chowProj_comp_hom B S hS X Wch c hc hsep Yo j n V e i]
      rfl
    obtain ⟨ρ, hρ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
      (X := preimageObj B S hS (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
        (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) i)
      (Y := Wch) _ hstruct
    exact ⟨ρ, by rw [hρ]; exact hfac⟩
  choose ρ hρ using hrho
  have hcomp : ∀ i, chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i ≫ ρ i =
      SpacesEtale.diagonalComplementProj B S hS X Wch c hc hsep (n + 1) V e i := by
    intro i
    have hlift : (BigFppfOver.toScheme B S hS).map
          (chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj i) ≫
        (chowProj B S hS X Wch c hc hsep Yo j n V e i ⁻¹ᵁ
          chartOpensRange B S hS j hj).ι =
      (BigFppfOver.toScheme B S hS).map (toSchemeImageObj B S hS
        (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)) :=
      openSubObjLift_toScheme_comp B S hS _ _ _ _
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    refine (cancel_mono ((BigFppfOver.toScheme B S hS).map j)).1 ?_
    rw [Functor.map_comp, Category.assoc, hρ i]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ chowProj B S hS X Wch c hc hsep Yo j n V e i) hlift).trans
        (toSchemeImageObj_comp_chowProj B S hS X Wch c hc hsep Yo j n V e i))
  refine ⟨ρ, hcomp, ?_⟩
  refine existsUnique_glueHom_unionPreimageObj_of_eq_on_dominant B S hS
    (chowImageObj B S hS X Wch c hc hsep Yo j n V e)
    (chowProj B S hS X Wch c hc hsep Yo j n V e) (chartOpensRange B S hS j hj) X.2 q hq
    (toSchemeImageObj B S hS (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)) hvo hvq hvdom
    (chowDenseLift B S hS X Wch c hc hsep Yo j n V e hj)
    (chowDenseLift_comp_preimageObjι B S hS X Wch c hc hsep Yo j n V e hj)
    (fun i ↦ yoneda.map (ρ i) ≫ c) fun i i' ↦ ?_
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hcomp i,
    hcomp i']
  exact SpacesEtale.yoneda_map_diagonalComplementProj_comp_chart_eq B S hS X Wch c hc hsep
    (n + 1) V e i i'

end AlgebraicGeometry.Space

end
