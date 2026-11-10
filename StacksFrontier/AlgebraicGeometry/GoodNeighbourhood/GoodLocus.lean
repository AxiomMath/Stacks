module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSections
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.SmoothDivisorDimension

/-!
# The locus where a closed subscheme is smooth of a given relative dimension

For a closed subscheme `T` of a scheme `X` over `S` and `r : ℕ`, the points of `T` at which `T`
is smooth of relative dimension `r` over `S` form an open of `T`,
`AlgebraicGeometry.GoodNeighbourhood.goodLocus`, on which `T` is smooth of relative dimension
`r`; a point `z` of `X` satisfies `SubschemeSmoothAt f T r z` exactly when it is the image of a
point of that open. This is the scheme to which the Bertini theorems are applied in the inductive
cut of SGA 4, Exposé XI, 3.3.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.goodLocus`: the union of the opens of `T` smooth of
  relative dimension `r`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.smoothOfRelativeDimension_goodLocus`: `T` is smooth of
  relative dimension `r` on its good locus.
* `AlgebraicGeometry.GoodNeighbourhood.exists_mem_goodLocus_of_subschemeSmoothAt`: a point where
  `T` is smooth of relative dimension `r` comes from the good locus.
* `AlgebraicGeometry.GoodNeighbourhood.subschemeSmoothAt_sup_of_comap`: smoothness of a cut
  `T ∩ E` read on an open `G` of `T` gives `SubschemeSmoothAt` for the closed subscheme `T ⊔ E`
  of `X`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **[Stacks, Tag 0B6Y] in the spelling `AlgebraicGeometry.zeroScheme`**: the zero scheme of a
pulled-back section is the inverse image of the zero scheme. This is
`Stacks.Divisors.zeroScheme_pullback`, whose statement uses the definitionally equal
`Stacks.Divisors.zeroScheme`. -/
theorem zeroScheme_pullback_eq_comap {X X' : Scheme.{u}} (g : X' ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤)) :
    zeroScheme X' ((Scheme.Modules.pullback g).obj L) (pullbackGlobalSections g L s) =
      (zeroScheme X L s).comap g :=
  Stacks.Divisors.zeroScheme_pullback g L s

variable {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (r : ℕ)

/-- **The good locus of `T`**: the union of the opens of the closed subscheme `T` on which `T` is
smooth of relative dimension `r` over the base. -/
noncomputable def goodLocus : T.subscheme.Opens :=
  ⨆ (U : T.subscheme.Opens) (_ : SmoothOfRelativeDimension r (U.ι ≫ T.subschemeι ≫ f)), U

/-- An open of `T` that is smooth of relative dimension `r` lies in the good locus. -/
private theorem le_goodLocus_of_smoothOfRelativeDimension {U : T.subscheme.Opens}
    (hU : SmoothOfRelativeDimension r (U.ι ≫ T.subschemeι ≫ f)) : U ≤ goodLocus f T r :=
  le_iSup₂_of_le (f := fun (V : T.subscheme.Opens)
    (_ : SmoothOfRelativeDimension r (V.ι ≫ T.subschemeι ≫ f)) => V) U hU le_rfl

/-- **`T` is smooth of relative dimension `r` on its good locus.** Smoothness of a given
relative dimension is local on the source. -/
theorem smoothOfRelativeDimension_goodLocus :
    SmoothOfRelativeDimension r ((goodLocus f T r).ι ≫ T.subschemeι ≫ f) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} r) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} r)
  set G := goodLocus f T r
  let ι := {U : T.subscheme.Opens // SmoothOfRelativeDimension r (U.ι ≫ T.subschemeι ≫ f)}
  have hle : ∀ U : ι, U.1 ≤ G := fun U => le_goodLocus_of_smoothOfRelativeDimension f T r U.2
  let 𝒰 : G.toScheme.OpenCover :=
    Scheme.Cover.mkOfCovers ι (fun U => U.1.toScheme) (fun U => T.subscheme.homOfLE (hle U))
      (fun y => by
        have hy : G.ι y ∈ G := y.2
        obtain ⟨U, hyU⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
        obtain ⟨hU, hyU⟩ := TopologicalSpace.Opens.mem_iSup.mp hyU
        refine ⟨⟨U, hU⟩, ⟨G.ι y, hyU⟩, ?_⟩
        apply G.ι.isOpenEmbedding.injective
        change (T.subscheme.homOfLE (hle ⟨U, hU⟩) ≫ G.ι) _ = _
        rw [Scheme.homOfLE_ι]
        rfl)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} r) 𝒰
    fun U => ?_
  change SmoothOfRelativeDimension r (T.subscheme.homOfLE (hle U) ≫ G.ι ≫ T.subschemeι ≫ f)
  rw [← Category.assoc, Scheme.homOfLE_ι]
  exact U.2

/-- **A point where `T` is smooth of relative dimension `r` comes from the good locus.** -/
theorem exists_mem_goodLocus_of_subschemeSmoothAt {z : X} (h : SubschemeSmoothAt f T r z) :
    ∃ y : (goodLocus f T r).toScheme, T.subschemeι ((goodLocus f T r).ι y) = z := by
  obtain ⟨y, hy, U, hyU, hU⟩ := h
  exact ⟨⟨y, le_goodLocus_of_smoothOfRelativeDimension f T r hU hyU⟩, hy⟩

/-- **Smoothness of a cut read on an open of `T`.** Let `G` be an open of the closed subscheme
`T`, and `E` a second closed subscheme of `X`. If the closed subscheme `T ∩ E` of `G` is smooth
of relative dimension `r` over the base, then `T ⊔ E` is smooth of relative dimension `r` at
every point of `G` lying on `E`. -/
theorem subschemeSmoothAt_sup_of_comap (E : X.IdealSheafData) (G : T.subscheme.Opens)
    (hsm : SmoothOfRelativeDimension r
      (((E.comap T.subschemeι).comap G.ι).subschemeι ≫ G.ι ≫ T.subschemeι ≫ f))
    (y : G.toScheme) (hy : T.subschemeι (G.ι y) ∈ E.support) :
    SubschemeSmoothAt f (T ⊔ E) r (T.subschemeι (G.ι y)) := by
  set J := E.comap T.subschemeι
  set K := J.comap G.ι
  obtain ⟨e', he'⟩ := Stacks.ChernCap42.exists_iso_comap_sup T E T.subschemeι (Iso.refl _)
    (by simp)
  set m := Scheme.IdealSheafData.subschemeMap K J G.ι (J.le_map_comap G.ι)
  have : IsOpenImmersion m := isOpenImmersion_subschemeMap_comap_of_isOpenImmersion J G.ι
  have hm : m ≫ J.subschemeι = K.subschemeι ≫ G.ι :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  set φ := m ≫ e'.hom
  have hφ : φ ≫ (T ⊔ E).subschemeι = K.subschemeι ≫ G.ι ≫ T.subschemeι := by
    simp only [φ, Category.assoc, he']
    rw [← Category.assoc, hm, Category.assoc]
  -- the point of `K` over `y`
  have hyK : y ∈ (K.support : Set G.toScheme) := by
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact hy
  rw [← Scheme.IdealSheafData.range_subschemeι] at hyK
  obtain ⟨y', hy'⟩ := hyK
  refine ⟨φ y', ?_, φ.opensRange, ⟨y', rfl⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy']
  · have hiso : φ.opensRange.ι = (Scheme.Hom.isoOpensRange φ).inv ≫ φ := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [hiso, Category.assoc, ← Category.assoc φ, hφ]
    have : SmoothOfRelativeDimension r (K.subschemeι ≫ G.ι ≫ T.subschemeι ≫ f) := hsm
    have h0 : SmoothOfRelativeDimension (0 + r) ((Scheme.Hom.isoOpensRange φ).inv ≫
        K.subschemeι ≫ G.ι ≫ T.subschemeι ≫ f) := inferInstance
    rw [zero_add] at h0
    simpa only [Category.assoc] using h0

end AlgebraicGeometry.GoodNeighbourhood

end
