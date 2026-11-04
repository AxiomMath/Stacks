module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ColimitDegeneration
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSmallSite

/-!
# Degeneration of the hypercovering spectral sequence on every page

`Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_zeroCocone_cohomologyPresheaf` says that
for `q > 0` the colimit over the hypercoverings of `X` of the **second** page `E₂^{p,q}` of the
spectral sequence of [Stacks, Tag 01GY] vanishes.  This file extends that to **every** page
`E_r^{p,q}` with `r ≥ 2`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.Functorial.pageHypercoveringDiagram`: the diagram
  `K ↦ E_r^{p,q}(K, 𝓕)` on the hypercoverings of `X`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.pageZeroCocone`: the cocone on it with the zero
  object as vertex.

## Main results

* `CategoryTheory.SpectralSequence.page_apply_eq_zero_of_cycles_apply_eq_zero`: a morphism of
  spectral sequences of abelian groups kills an element of the `(r+1)`-st page as soon as it kills
  a cycle representing it on the `r`-th page.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_pageTwo_eq_zero`: for
  `q > 0`, every element of the second page `E₂^{p,q}(K, 𝓕)` dies after a refinement of `K`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_page_eq_zero`: **for
  `q > 0`, every `r ≥ 2` and every `p`, every element of `E_r^{p,q}(K, 𝓕)` dies after a refinement
  of `K`.**
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_pageZeroCocone`:
  **`colim_K E_r^{p,q}(K, 𝓕) = 0` for `q > 0` and every `r ≥ 2`.**

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod
open scoped ZeroObject

universe v

namespace CategoryTheory.SpectralSequence

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- **Every element of a page is the class of a cycle of the previous page**, through the
identification `E_{r+1}^{pq} ≅ Ker(d_r)/Im(d_r)` of `CategoryTheory.SpectralSequence.iso`. -/
theorem exists_cycles_homologyπ_eq (E : SpectralSequence AddCommGrpCat.{v} c r₀)
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (x : ToType ((E.page r' hr').X pq)) :
    ∃ z : ToType ((E.page r hr).cycles pq),
      ConcreteCategory.hom ((E.page r hr).homologyπ pq) z =
        ConcreteCategory.hom (E.iso r r' pq hrr' hr).inv x :=
  (AddCommGrpCat.epi_iff_surjective ((E.page r hr).homologyπ pq)).1 inferInstance _

/-- **A morphism of spectral sequences kills an element of the `(r+1)`-st page as soon as it kills
a cycle representing it on the `r`-th page.** -/
theorem page_apply_eq_zero_of_cycles_apply_eq_zero
    {E E' : SpectralSequence AddCommGrpCat.{v} c r₀} (ψ : E ⟶ E')
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (x : ToType ((E.page r' hr').X pq)) (z : ToType ((E.page r hr).cycles pq))
    (hz : ConcreteCategory.hom ((E.page r hr).homologyπ pq) z =
      ConcreteCategory.hom (E.iso r r' pq hrr' hr).inv x)
    (hzero : ConcreteCategory.hom ((ψ.hom r hr).f pq)
      (ConcreteCategory.hom ((E.page r hr).iCycles pq) z) = 0) :
    ConcreteCategory.hom ((ψ.hom r' hr').f pq) x = 0 := by
  have hcyc : ConcreteCategory.hom
      (HomologicalComplex.cyclesMap (ψ.hom r hr) pq) z = 0 := by
    refine (AddCommGrpCat.mono_iff_injective ((E'.page r hr).iCycles pq)).1 inferInstance ?_
    rw [map_zero, ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
    exact hzero
  have ht : ConcreteCategory.hom (E.iso r r' pq hrr' hr).hom
      (ConcreteCategory.hom (E.iso r r' pq hrr' hr).inv x) = x := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have hhom : ConcreteCategory.hom (HomologicalComplex.homologyMap (ψ.hom r hr) pq)
      (ConcreteCategory.hom (E.iso r r' pq hrr' hr).inv x) = 0 := by
    rw [← hz, ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply, hcyc, map_zero]
  have hcomm := ConcreteCategory.congr_hom (ψ.comm r r' pq hrr' hr)
    (ConcreteCategory.hom (E.iso r r' pq hrr' hr).inv x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hhom, map_zero, ht] at hcomm
  exact hcomm.symm

end CategoryTheory.SpectralSequence

namespace Stacks.CategoryTheory.Hypercovering.Functorial

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- `CategoryTheory.Sheaf.hasExt_of_smallSite` as a local instance. -/
local instance hasExtSmallSitePage :
    HasExt.{v} (Sheaf J.toGrothendieck AddCommGrpCat.{v}) :=
  Sheaf.hasExt_of_smallSite J.toGrothendieck

/-- **The diagram `K ↦ E_r^{p,q}(K, 𝓕)` on the hypercoverings of `X`**: the `(p, q)` term of the
`r`-th page of the spectral sequence of clause (3) of [Stacks, Tag 01GY], with the coefficient
sheaf `𝓕` held fixed. -/
abbrev pageHypercoveringDiagram (r : ℤ) (hr : 2 ≤ r) (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (HypercoveringCat X J)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  _root_.CategoryTheory.Prod.sectL (HypercoveringCat X J)ᵒᵖ F ⋙
    hypercoveringSpectralSequence X J ⋙
      _root_.CategoryTheory.SpectralSequence.pageFunctor _ _ 2 r hr ⋙
        HomologicalComplex.eval _ _ (p, q)

/-- On a morphism of hypercoverings the diagram acts by the `(p, q)` component of the `r`-th page
of the morphism of spectral sequences. -/
lemma pageHypercoveringDiagram_map (r : ℤ) (hr : 2 ≤ r) (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (pageHypercoveringDiagram X J r hr p q F).map g =
      (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom r hr).f (p, q) :=
  rfl

/-- The second page of the spectral sequence of [Stacks, Tag 01GY] is `Ȟ^p(K, H^q(𝓕))`, naturally
in the hypercovering. -/
lemma pageTwo_naturality (p q : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (p, q) ≫
        (hypercoveringPageTwoIso.{v} X J p q).hom.app (L, F) =
      (hypercoveringPageTwoIso.{v} X J p q).hom.app (K, F) ≫
        (pageTwoHypercovering.{v} X J p q).map (g ×ₘ 𝟙 F) :=
  (hypercoveringPageTwoIso.{v} X J p q).hom.naturality (g ×ₘ 𝟙 F)

/-- On a morphism of hypercoverings the second-page functor of [Stacks, Tag 01GY] is the canonical
pullback map on Čech cohomology. -/
lemma pageTwoHypercovering_map (p q : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (pageTwoHypercovering.{v} X J p q).map (g ×ₘ 𝟙 F) =
      ((cechCohomologyOverBifunctor.{v} X p).map g.unop.hom.op).app
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck q).obj F) :=
  pageTwoSmallSite_map_hypercovering' J.toGrothendieck X g.unop.hom.op F p q

/-- **The second page of the spectral sequence of [Stacks, Tag 01GY] at `(p, q)` is
`Ȟ^p(K, H^q(𝓕))`**, as a single isomorphism whose source is spelled the way the spectral sequence
presents the page. -/
def pageTwoIsoHypercovering (p q : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (K : (HypercoveringCat X J)ᵒᵖ) :
    (((hypercoveringSpectralSequence X J).obj (K, F)).page 2 le_rfl).X (p, q) ≅
      (pageTwoHypercovering.{v} X J p q).obj (K, F) :=
  (hypercoveringPageTwoIso.{v} X J p q).app (K, F)

/-- `pageTwoIsoHypercovering` is natural in the hypercovering. -/
lemma pageTwoIsoHypercovering_naturality (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (p, q) ≫
        (pageTwoIsoHypercovering X J p q F L).hom =
      (pageTwoIsoHypercovering X J p q F K).hom ≫
        (pageTwoHypercovering.{v} X J p q).map (g ×ₘ 𝟙 F) :=
  pageTwo_naturality X J p q F g

/-- **Every element of the second page `E₂^{p,q}` dies after a refinement of the hypercovering**,
for `q > 0`. -/
theorem exists_hypercovering_map_pageTwo_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : (HypercoveringCat X J)ᵒᵖ)
    (x : ToType ((((hypercoveringSpectralSequence X J).obj (K, F)).page 2 le_rfl).X (p, q))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom
        ((((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (p, q)) x = 0 := by
  obtain ⟨M, hM, f, hf⟩ := exists_hypercovering_map_cechCohomology_eq_zero
    (isLocallyZero_cohomologyPresheaf J F q hq) K.unop.obj K.unop.property p
    (ConcreteCategory.hom (pageTwoIsoHypercovering X J p q F K).hom x)
  refine ⟨op (⟨M, hM⟩ : HypercoveringCat X J),
    Quiver.Hom.op (ObjectProperty.homMk f : (⟨M, hM⟩ : HypercoveringCat X J) ⟶ K.unop), ?_⟩
  refine (AddCommGrpCat.mono_iff_injective (pageTwoIsoHypercovering X J p q F
    (op (⟨M, hM⟩ : HypercoveringCat X J))).hom).1 inferInstance ?_
  rw [map_zero, ← ConcreteCategory.comp_apply, pageTwoIsoHypercovering_naturality,
    ConcreteCategory.comp_apply, pageTwoHypercovering_map]
  exact hf

/-- **Every element of the page `E_{2+n}^{p,q}` dies after a refinement of the hypercovering**, for
`q > 0` and `n : ℕ`. -/
theorem exists_hypercovering_map_pageAdd_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ∀ (hr : 2 ≤ 2 + (n : ℤ)) (p : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
      (x : ToType ((((hypercoveringSpectralSequence X J).obj (K, F)).page (2 + (n : ℤ)) hr).X
        (p, q))),
      ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
        ConcreteCategory.hom ((((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom
          (2 + (n : ℤ)) hr).f (p, q)) x = 0 := by
  induction n with
  | zero =>
    intro _ p K x
    exact exists_hypercovering_map_pageTwo_eq_zero X J F q hq p K x
  | succ n ih =>
    intro hr p K x
    obtain ⟨z, hz⟩ := _root_.CategoryTheory.SpectralSequence.exists_cycles_homologyπ_eq
      ((hypercoveringSpectralSequence X J).obj (K, F)) (2 + (n : ℤ)) (2 + ((n + 1 : ℕ) : ℤ))
      (p, q) (by omega) (by omega) hr x
    obtain ⟨L, g, hw⟩ := ih (by omega) p K
      (ConcreteCategory.hom ((((hypercoveringSpectralSequence X J).obj (K, F)).page
        (2 + (n : ℤ)) (by omega)).iCycles (p, q)) z)
    exact ⟨L, g,
      _root_.CategoryTheory.SpectralSequence.page_apply_eq_zero_of_cycles_apply_eq_zero
        ((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)) _ _ (p, q) _ _ _ x z hz hw⟩

/-- **For `q > 0` and every page `r ≥ 2`, every element of `E_r^{p,q}` dies after a refinement of
the hypercovering.** -/
theorem exists_hypercovering_map_page_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (r : ℤ) (hr : 2 ≤ r)
    (p : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
    (x : ToType ((((hypercoveringSpectralSequence X J).obj (K, F)).page r hr).X (p, q))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom
        ((((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom r hr).f (p, q)) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = 2 + (n : ℤ) := ⟨(r - 2).toNat, by omega⟩
  exact exists_hypercovering_map_pageAdd_eq_zero X J F q hq n hr p K x

/-! ### The colimit over the hypercoverings of a page -/

/-- **The cocone on the diagram `K ↦ E_r^{p,q}(K, 𝓕)` with the zero object as vertex.** -/
def pageZeroCocone (r : ℤ) (hr : 2 ≤ r) (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    Cocone (pageHypercoveringDiagram X J r hr p q F) :=
  Cocone.mk 0 { app := fun _ => 0, naturality := fun _ _ _ => by simp }

/-- **Every leg of every cocone on the diagram `K ↦ E_r^{p,q}(K, 𝓕)` vanishes**, for `q > 0` and
`r ≥ 2`. -/
theorem page_cocone_ι_app_eq_zero [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (r : ℤ) (hr : 2 ≤ r)
    (p : ℕ) (s : Cocone (pageHypercoveringDiagram X J r hr p q F))
    (K : (HypercoveringCat X J)ᵒᵖ) : s.ι.app K = 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  obtain ⟨L, g, hg⟩ := exists_hypercovering_map_page_eq_zero X J F q hq r hr p K x
  have hw : ConcreteCategory.hom ((pageHypercoveringDiagram X J r hr p q F).map g) x = 0 := hg
  rw [← ConcreteCategory.congr_hom (s.w g) x, ConcreteCategory.comp_apply, hw, map_zero]
  simp

/-- **`colim_K E_r^{p,q}(K, 𝓕) = 0` for `q > 0` and every page `r ≥ 2`**, the colimit being over
all hypercoverings of `X`: the cocone with the zero object as vertex is a colimit cocone, every leg
of every cocone being zero. -/
def isColimit_pageZeroCocone [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (r : ℤ) (hr : 2 ≤ r)
    (p : ℕ) : IsColimit (pageZeroCocone X J r hr p q F) where
  desc _ := 0
  fac s K := zero_comp.trans (page_cocone_ι_app_eq_zero X J F q hq r hr p s K).symm
  uniq _ m _ := (isZero_zero AddCommGrpCat.{v}).eq_of_src m 0

end Stacks.CategoryTheory.Hypercovering.Functorial

end
