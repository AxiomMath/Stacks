module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.TrivialBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatAmbient
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateChart
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# The ambient space of Tag 0F97 is an affine-space bundle of rank two, with an explicit chart

Let `Y` be a scheme and let `L₁` and `L₂` be invertible `𝒪_Y`-modules. The scheme of [Stacks, Tag
0F97] is cut out by one equation inside the fibre product
`T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line bundles of [Stacks, Tag 01M2], built in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic`. This file proves that the structure
morphism `q : T ⟶ Y` of that fibre product is an **affine-space bundle of rank two**, and
produces the **explicit polynomial chart** the tag's own proof works with: over an affine open `V`
of `Y` trivializing both inverse modules, `q^{-1}(V)` is affine with

  `Γ(T, q^{-1}V) ≅ Γ(Y, V)[z₁, z₂]`,

the structure map going to the constants and the two variables being the fibre coordinates of the
two factors.

## Main definitions

* `Stacks.Chow.affineSpaceSectionsIso`: the global sections of `𝔸^n` over an affine base, as a
  polynomial ring.
* `Stacks.Chow.affineSpaceIsoOfSectionsIso`: conversely, an affine scheme over an affine base
  whose sections are presented as a polynomial ring over those of the base, compatibly with the
  structure map, **is** affine space over it.
* `Stacks.Chow.pullbackAffineSpaceSumIso`: a fibre product of two affine spaces over the base is
  affine space on the sum of the two index types.
* `Stacks.Chow.TensorZeroScheme.lineBundleChart`: **the polynomial chart `Γ(L(M), q^{-1}V) ≅
  Γ(Y, V)[z]` of the line bundle of an invertible module** over an affine open trivializing
  `M^{⊗ -1}`.
* `Stacks.Chow.TensorZeroScheme.ambientChart`: **the polynomial chart
  `Γ(T, q^{-1}V) ≅ Γ(Y, V)[z₁, z₂]` of the ambient space of Tag 0F97.**

## Main results

* `Stacks.Chow.isPullback_affineSpace_sum`: affine space on a sum index type is the fibre product
  of the two affine spaces over the base.
* `Stacks.Chow.isTrivialAffineSpaceBundle_fst_comp`: the structure morphism of a fibre product of
  two globally trivial affine-space bundles over the same base is globally trivial, of the sum of
  the two ranks.
* `Stacks.Chow.isTrivialAffineSpaceBundle_morphismRestrict_of_le`: a globally trivial
  affine-space bundle over an open subscheme of the target stays one over a smaller open
  subscheme.
* `Stacks.Chow.TensorZeroScheme.isAffineSpaceBundle_totalProj`: **the structure morphism
  `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is an affine-space bundle of rank two.**
* `Stacks.Chow.TensorZeroScheme.isAffineOpen_totalProj_preimage`: the inverse image of such an
  affine open is affine.
* `Stacks.Chow.TensorZeroScheme.ambientChart_app`: the chart carries the structure map
  `Γ(Y, V) ⟶ Γ(T, q^{-1}V)` to `MvPolynomial.C`.
* `Stacks.Chow.TensorZeroScheme.ambientChart_app_firstProj` and
  `ambientChart_app_secondProj`: **which variable belongs to which factor** — the variable of the
  chart of the first (second) line bundle is carried by restriction along `firstProj`
  (`secondProj`) to `MvPolynomial.X 0` (`MvPolynomial.X 1`).
* `Stacks.Chow.TensorZeroScheme.exists_affineOpen_basis_inverseModule`: around every point of `Y`
  there is an affine open carrying bases of both inverse modules, which is what the chart needs.

## Implementation notes

*Rank two.* Both line bundles are rank-one affine-space bundles by
`Stacks.LineBundle.isAffineSpaceBundle_lineBundleProj`, but over *different* trivializing opens of
`Y`; the two are intersected, which is what
`Stacks.Chow.isTrivialAffineSpaceBundle_morphismRestrict_of_le` is for. Over the intersection the
restriction of `q` is the composite of the restriction of the first projection with the
restriction of the first line bundle's structure morphism
(`AlgebraicGeometry.morphismRestrict_comp`), and that composite sits in a cartesian square
exhibiting it as the fibre product of the two restricted line bundles
(`Stacks.Chow.isPullback_restrict_pullback`, whose second leg is written as a
`AlgebraicGeometry.Scheme.Hom.resLE` so that its sections are computable).

The missing piece of the Mathlib `AffineSpace` API is the identification of `𝔸^{a+b}` with
`𝔸^a ×_S 𝔸^b`; it is proved here in the index-type form
`Stacks.Chow.isPullback_affineSpace_sum`, directly from the universal property
`AlgebraicGeometry.AffineSpace.homOfVector` of affine space, and transported to the numeral form
by `Stacks.Chow.affineSpaceReindexIso` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity` along
`finSumFinEquiv`.

*The chart.* The chart of one line bundle is the universal map of its relative spectrum,
`Stacks.RelativeSpec.universalAlgebraMap`, which identifies `Γ(L(M), q^{-1}V)` with the sections
of `Sym(M^{⊗ -1})` over `V` and carries the structure morphism of the relative spectrum to the
structure map of the algebra (`Stacks.RelativeSpec.toBase_app`), followed by the polynomial
presentation `Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv` of those sections
attached to a basis of `Γ(M^{⊗ -1}, V)`. That chart is then fed back through
`Stacks.Chow.affineSpaceIsoOfSectionsIso` to present `q^{-1}(V)` as an affine line over `V` whose
coordinate **is** the variable of the chart, and the chart of the ambient space is read off the
resulting presentation of the fibre product as `𝔸^{1+1}_V`. This is what makes the two variables
traceable to the two factors; an abstract trivialization, such as the one
`Stacks.Chow.exists_iso_affineSpace_of_mvPolynomialSections` produces, determines no coordinates.

*Why `resLE` and `appTop`.* A goal mentioning `Γ(V, ⊤)` for an open subscheme `V` is not
type-correct at `implicit` transparency — `Scheme.Opens.toScheme` is semireducible — so `rw`
fails its motive type-check on goals elaboration crosses without difficulty, exactly as recorded
in `StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMap`. Two devices keep the rewrites
usable: the sections of a restriction are quoted through `Stacks.Chow.morphismRestrict_appTop'`,
whose two sides have the *same* type (unlike `AlgebraicGeometry.Scheme.Hom.resLE_app_top`, where
they are only definitionally equal, so that it is only applied in term mode), and the final
assembly of each chart identity is written in term mode with `congrArg` and
`CategoryTheory.Iso.inv_hom_id_apply`.

*What this does not give.* The ideal of the zero scheme of a fibre coordinate inside the chart is
not computed here, and neither is the equation `z₁z₂ - q^*s` of the tag; the chart is the input
those need.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LineBundle (lineBundleProj)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow

open AlgebraicGeometry.AffineSpace

/-! ### Affine space on a sum index type -/

/-- **Affine space on a sum index type is the fibre product of the two affine spaces.** The two
projections are the reindexings along the two inclusions of the sum, and a pair of morphisms to
the two factors agreeing over the base is a single morphism given by the two families of
coordinate functions. -/
theorem isPullback_affineSpace_sum (n₁ n₂ : Type u) (S : Scheme.{u}) :
    IsPullback (reindex (Sum.inl : n₁ → n₁ ⊕ n₂) S) (reindex (Sum.inr : n₂ → n₁ ⊕ n₂) S)
      (𝔸(n₁; S) ↘ S) (𝔸(n₂; S) ↘ S) := by
  have w : reindex (Sum.inl : n₁ → n₁ ⊕ n₂) S ≫ (𝔸(n₁; S) ↘ S) =
      reindex (Sum.inr : n₂ → n₁ ⊕ n₂) S ≫ (𝔸(n₂; S) ↘ S) := by
    rw [reindex_over, reindex_over]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => homOfVector (s.fst ≫ (𝔸(n₁; S) ↘ S))
      (Sum.elim (fun i => s.fst.appTop (coord S i)) (fun j => s.snd.appTop (coord S j))))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · refine hom_ext ?_ fun i => ?_
    · rw [Category.assoc, reindex_over, homOfVector_over]
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        homOfVector_appTop_coord, Sum.elim_inl]
  · refine hom_ext ?_ fun j => ?_
    · rw [Category.assoc, reindex_over, homOfVector_over, s.condition]
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
        homOfVector_appTop_coord, Sum.elim_inr]
  · refine hom_ext ?_ fun k => ?_
    · rw [homOfVector_over, ← hm₁, Category.assoc, reindex_over]
    · rw [homOfVector_appTop_coord]
      obtain i | j := k
      · rw [← hm₁]
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          Sum.elim_inl]
      · rw [← hm₂]
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          Sum.elim_inr]

/-! ### A fibre product of two globally trivial bundles -/

/-- **A fibre product of two morphisms presented as affine spaces over the base is the fibre
product of the two affine spaces.** -/
theorem isPullback_affineSpace_of_iso {P W₁ W₂ V : Scheme.{u}} {a : P ⟶ W₁} {b : P ⟶ W₂}
    {g₁ : W₁ ⟶ V} {g₂ : W₂ ⟶ V} (hsq : IsPullback a b g₁ g₂) {n₁ n₂ : Type u}
    {e₁ : W₁ ≅ 𝔸(n₁; V)} (he₁ : e₁.hom ≫ (𝔸(n₁; V) ↘ V) = g₁)
    {e₂ : W₂ ≅ 𝔸(n₂; V)} (he₂ : e₂.hom ≫ (𝔸(n₂; V) ↘ V) = g₂) :
    IsPullback (a ≫ e₁.hom) (b ≫ e₂.hom) (𝔸(n₁; V) ↘ V) (𝔸(n₂; V) ↘ V) := by
  have hiso₁ : IsPullback e₁.hom g₁ (𝔸(n₁; V) ↘ V) (𝟙 V) :=
    IsPullback.of_horiz_isIso ⟨by rw [he₁, Category.comp_id]⟩
  have hiso₂ : IsPullback e₂.hom g₂ (𝔸(n₂; V) ↘ V) (𝟙 V) :=
    IsPullback.of_horiz_isIso ⟨by rw [he₂, Category.comp_id]⟩
  have hA : IsPullback (a ≫ e₁.hom) b (𝔸(n₁; V) ↘ V) g₂ := by
    have h := hsq.paste_horiz hiso₁
    rwa [Category.comp_id] at h
  have h := hA.flip.paste_horiz hiso₂
  rw [Category.comp_id] at h
  exact h.flip

/-- **The fibre product of two morphisms presented as affine spaces over the base is affine space
on the sum of the two index types.** -/
def pullbackAffineSpaceSumIso {P W₁ W₂ V : Scheme.{u}} {a : P ⟶ W₁} {b : P ⟶ W₂}
    {g₁ : W₁ ⟶ V} {g₂ : W₂ ⟶ V} (hsq : IsPullback a b g₁ g₂) {n₁ n₂ : Type u}
    {e₁ : W₁ ≅ 𝔸(n₁; V)} (he₁ : e₁.hom ≫ (𝔸(n₁; V) ↘ V) = g₁)
    {e₂ : W₂ ≅ 𝔸(n₂; V)} (he₂ : e₂.hom ≫ (𝔸(n₂; V) ↘ V) = g₂) :
    P ≅ 𝔸(n₁ ⊕ n₂; V) :=
  (isPullback_affineSpace_of_iso hsq he₁ he₂).isoIsPullback _ _
    (isPullback_affineSpace_sum n₁ n₂ V)

section

variable {P W₁ W₂ V : Scheme.{u}} {a : P ⟶ W₁} {b : P ⟶ W₂} {g₁ : W₁ ⟶ V} {g₂ : W₂ ⟶ V}
  (hsq : IsPullback a b g₁ g₂) {n₁ n₂ : Type u} {e₁ : W₁ ≅ 𝔸(n₁; V)}
  (he₁ : e₁.hom ≫ (𝔸(n₁; V) ↘ V) = g₁) {e₂ : W₂ ≅ 𝔸(n₂; V)}
  (he₂ : e₂.hom ≫ (𝔸(n₂; V) ↘ V) = g₂)

/-- The comparison with affine space on the sum index type, followed by the projection to the
first summand, is the first projection followed by its trivialization. -/
theorem pullbackAffineSpaceSumIso_hom_reindex_inl :
    (pullbackAffineSpaceSumIso hsq he₁ he₂).hom ≫ reindex (Sum.inl : n₁ → n₁ ⊕ n₂) V =
      a ≫ e₁.hom :=
  (isPullback_affineSpace_of_iso hsq he₁ he₂).isoIsPullback_hom_fst _ _
    (isPullback_affineSpace_sum n₁ n₂ V)

/-- The comparison with affine space on the sum index type, followed by the projection to the
second summand, is the second projection followed by its trivialization. -/
theorem pullbackAffineSpaceSumIso_hom_reindex_inr :
    (pullbackAffineSpaceSumIso hsq he₁ he₂).hom ≫ reindex (Sum.inr : n₂ → n₁ ⊕ n₂) V =
      b ≫ e₂.hom :=
  (isPullback_affineSpace_of_iso hsq he₁ he₂).isoIsPullback_hom_snd _ _
    (isPullback_affineSpace_sum n₁ n₂ V)

/-- The comparison with affine space on the sum index type lies over the base. -/
theorem pullbackAffineSpaceSumIso_hom_over :
    (pullbackAffineSpaceSumIso hsq he₁ he₂).hom ≫ (𝔸(n₁ ⊕ n₂; V) ↘ V) = a ≫ g₁ := by
  rw [← reindex_over (Sum.inl : n₁ → n₁ ⊕ n₂) V, ← Category.assoc,
    pullbackAffineSpaceSumIso_hom_reindex_inl, Category.assoc, he₁]

/-- The comparison with affine space on the sum index type carries the coordinates of the first
summand to the coordinates of the first factor. -/
theorem pullbackAffineSpaceSumIso_hom_appTop_coord_inl (i : n₁) :
    (pullbackAffineSpaceSumIso hsq he₁ he₂).hom.appTop (coord V (Sum.inl i)) =
      a.appTop (e₁.hom.appTop (coord V i)) := by
  have h2 := congrArg (fun k : P ⟶ 𝔸(n₁; V) => k.appTop (coord V i))
    (pullbackAffineSpaceSumIso_hom_reindex_inl hsq he₁ he₂)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord] using h2

/-- The comparison with affine space on the sum index type carries the coordinates of the second
summand to the coordinates of the second factor. -/
theorem pullbackAffineSpaceSumIso_hom_appTop_coord_inr (j : n₂) :
    (pullbackAffineSpaceSumIso hsq he₁ he₂).hom.appTop (coord V (Sum.inr j)) =
      b.appTop (e₂.hom.appTop (coord V j)) := by
  have h2 := congrArg (fun k : P ⟶ 𝔸(n₂; V) => k.appTop (coord V j))
    (pullbackAffineSpaceSumIso_hom_reindex_inr hsq he₁ he₂)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord] using h2

end

/-- **The structure morphism of a fibre product of two globally trivial affine-space bundles is a
globally trivial affine-space bundle of the sum of the two ranks.** The two trivializations
replace the two factors by affine spaces, and affine space on the sum of the two index sets is
their fibre product. -/
theorem isTrivialAffineSpaceBundle_fst_comp {P W₁ W₂ V : Scheme.{u}} {a : P ⟶ W₁} {b : P ⟶ W₂}
    {g₁ : W₁ ⟶ V} {g₂ : W₂ ⟶ V} (hsq : IsPullback a b g₁ g₂) (r₁ r₂ : ℕ)
    (h₁ : IsTrivialAffineSpaceBundle g₁ r₁) (h₂ : IsTrivialAffineSpaceBundle g₂ r₂) :
    IsTrivialAffineSpaceBundle (a ≫ g₁) (r₁ + r₂) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  let ε : ULift.{u} (Fin r₁) ⊕ ULift.{u} (Fin r₂) ≃ ULift.{u} (Fin (r₁ + r₂)) :=
    (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)
  refine ⟨pullbackAffineSpaceSumIso hsq he₁ he₂ ≪≫ affineSpaceReindexIso ε V, ?_⟩
  change ((pullbackAffineSpaceSumIso hsq he₁ he₂).hom ≫ reindex ε.symm V) ≫ _ = _
  rw [Category.assoc, reindex_over, pullbackAffineSpaceSumIso_hom_over]

/-- **A globally trivial affine-space bundle over an open subscheme of the target stays one over a
smaller open subscheme.** Restricting to a smaller open subscheme is restricting the restriction,
which is a base change of it along an open immersion. -/
theorem isTrivialAffineSpaceBundle_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hVU : V ≤ U) (r : ℕ) (h : IsTrivialAffineSpaceBundle (f ∣_ U) r) :
    IsTrivialAffineSpaceBundle (f ∣_ V) r := by
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  have hres : IsTrivialAffineSpaceBundle ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) r :=
    isTrivialAffineSpaceBundle_of_isPullback
      (isPullback_morphismRestrict (f ∣_ U) (U.ι ⁻¹ᵁ V)).flip r h
  exact isTrivialAffineSpaceBundle_of_arrowIso
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f himg).symm r hres

/-! ### The polynomial chart of affine space over an affine base -/

/-- The global sections of two isomorphic schemes are isomorphic. -/
def schemeSectionsIso {W Z : Scheme.{u}} (e : W ≅ Z) : Γ(W, ⊤) ≅ Γ(Z, ⊤) where
  hom := e.inv.appTop
  inv := e.hom.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
  inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]

/-- **The global sections of affine `n`-space over an affine scheme are the polynomial ring in
`n` variables over the global sections of the base.** -/
def affineSpaceSectionsIso (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    Γ(𝔸(n; S), ⊤) ≅ CommRingCat.of (MvPolynomial n Γ(S, ⊤)) where
  hom := (isoOfIsAffine n S).inv.appTop ≫ (Scheme.ΓSpecIso _).hom
  inv := (Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine n S).hom.appTop
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
      Scheme.Hom.id_appTop]
  inv_hom_id := by
    have h : (isoOfIsAffine n S).hom.appTop ≫ (isoOfIsAffine n S).inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
    rw [Category.assoc, ← Category.assoc ((isoOfIsAffine n S).hom.appTop), h, Category.id_comp,
      Iso.inv_hom_id]

/-- The inverse of the polynomial chart of affine space evaluates a polynomial at the standard
coordinates. -/
theorem affineSpaceSectionsIso_inv (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    (affineSpaceSectionsIso n S).inv =
      CommRingCat.ofHom
        (MvPolynomial.eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)) := by
  change (Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine n S).hom.appTop = _
  rw [isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]

/-- The polynomial chart of affine space carries the `i`-th variable to the `i`-th coordinate. -/
theorem affineSpaceSectionsIso_inv_X (n : Type u) (S : Scheme.{u}) [IsAffine S] (i : n) :
    (affineSpaceSectionsIso n S).inv (MvPolynomial.X i) = coord S i := by
  rw [affineSpaceSectionsIso_inv]
  simp only [ConcreteCategory.hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

/-- The polynomial chart of affine space carries a constant to the corresponding section of the
base. -/
theorem affineSpaceSectionsIso_inv_C (n : Type u) (S : Scheme.{u}) [IsAffine S] (s : Γ(S, ⊤)) :
    (affineSpaceSectionsIso n S).inv (MvPolynomial.C s) = (𝔸(n; S) ↘ S).appTop s := by
  rw [affineSpaceSectionsIso_inv]
  simp only [ConcreteCategory.hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

/-- **The polynomial chart of a scheme presented as affine space over an affine base.** -/
def affineSpaceChartIso {W S : Scheme.{u}} [IsAffine S] {n : Type u} (e : W ≅ 𝔸(n; S)) :
    Γ(W, ⊤) ≅ CommRingCat.of (MvPolynomial n Γ(S, ⊤)) :=
  schemeSectionsIso e ≪≫ affineSpaceSectionsIso n S

/-- The chart of a scheme presented as affine space carries the `i`-th variable to the pullback of
the `i`-th coordinate. -/
theorem affineSpaceChartIso_inv_X {W S : Scheme.{u}} [IsAffine S] {n : Type u} (e : W ≅ 𝔸(n; S))
    (i : n) : (affineSpaceChartIso e).inv (MvPolynomial.X i) = e.hom.appTop (coord S i) := by
  change (schemeSectionsIso e).inv ((affineSpaceSectionsIso n S).inv (MvPolynomial.X i)) = _
  rw [affineSpaceSectionsIso_inv_X]
  rfl

/-- The chart of a scheme presented as affine space over an affine base carries a constant to the
pullback of the corresponding section of the base. -/
theorem affineSpaceChartIso_inv_C {W S : Scheme.{u}} [IsAffine S] {n : Type u} {π : W ⟶ S}
    (e : W ≅ 𝔸(n; S)) (he : e.hom ≫ (𝔸(n; S) ↘ S) = π) (s : Γ(S, ⊤)) :
    (affineSpaceChartIso e).inv (MvPolynomial.C s) = π.appTop s := by
  change (schemeSectionsIso e).inv ((affineSpaceSectionsIso n S).inv (MvPolynomial.C s)) = _
  rw [affineSpaceSectionsIso_inv_C, ← he]
  change e.hom.appTop ((𝔸(n; S) ↘ S).appTop s) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-! ### Affine space from a polynomial presentation of the sections -/

section

variable {W S : Scheme.{u}} [IsAffine W] [IsAffine S] (π : W ⟶ S) {n : Type u}
  (Φ : Γ(W, ⊤) ≅ CommRingCat.of (MvPolynomial n Γ(S, ⊤)))
  (hΦ : π.appTop ≫ Φ.hom = CommRingCat.ofHom MvPolynomial.C)

omit [IsAffine W] [IsAffine S] in
include hΦ in
/-- A polynomial presentation of the sections sending the structure map to the constants carries a
constant back to the corresponding section of the base. -/
theorem sectionsIso_inv_C (s : Γ(S, ⊤)) : Φ.inv (MvPolynomial.C s) = π.appTop s := by
  have h : Φ.hom (π.appTop s) = MvPolynomial.C s := by
    rw [← CommRingCat.comp_apply, hΦ, ConcreteCategory.hom_ofHom]
  rw [← h, Iso.hom_inv_id_apply]

/-- The morphism to affine space attached to a polynomial presentation of the sections of an
affine scheme over an affine base. -/
def affineSpaceHomOfSectionsIso : W ⟶ 𝔸(n; S) :=
  homOfVector π fun i => Φ.inv (MvPolynomial.X i)

omit [IsAffine W] in
include hΦ in
/-- The morphism to affine space attached to a polynomial presentation of the sections induces,
on global sections, that presentation. -/
theorem affineSpaceHomOfSectionsIso_appTop :
    (affineSpaceHomOfSectionsIso π Φ).appTop = (affineSpaceSectionsIso n S).hom ≫ Φ.inv := by
  rw [← Iso.inv_comp_eq]
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · change (affineSpaceHomOfSectionsIso π Φ).appTop
        ((affineSpaceSectionsIso n S).inv (MvPolynomial.C r)) = Φ.inv (MvPolynomial.C r)
    rw [affineSpaceSectionsIso_inv_C, sectionsIso_inv_C π Φ hΦ, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, affineSpaceHomOfSectionsIso, homOfVector_over]
  · change (affineSpaceHomOfSectionsIso π Φ).appTop
        ((affineSpaceSectionsIso n S).inv (MvPolynomial.X i)) = Φ.inv (MvPolynomial.X i)
    rw [affineSpaceSectionsIso_inv_X, affineSpaceHomOfSectionsIso, homOfVector_appTop_coord]

include hΦ in
/-- The morphism to affine space attached to a polynomial presentation of the sections of an
affine scheme over an affine base is an isomorphism. -/
theorem isIso_affineSpaceHomOfSectionsIso : IsIso (affineSpaceHomOfSectionsIso π Φ) := by
  have happ : IsIso (affineSpaceHomOfSectionsIso π Φ).appTop := by
    rw [affineSpaceHomOfSectionsIso_appTop π Φ hΦ]
    infer_instance
  have hfac : W.isoSpec.hom ≫ Spec.map (affineSpaceHomOfSectionsIso π Φ).appTop ≫
      (𝔸(n; S)).isoSpec.inv = affineSpaceHomOfSectionsIso π Φ := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [← hfac]
  infer_instance

/-- **An affine scheme over an affine base whose sections are presented as a polynomial ring over
those of the base, compatibly with the structure map, is affine space over that base.** -/
def affineSpaceIsoOfSectionsIso : W ≅ 𝔸(n; S) :=
  haveI := isIso_affineSpaceHomOfSectionsIso π Φ hΦ
  asIso (affineSpaceHomOfSectionsIso π Φ)

/-- The presentation of an affine scheme as affine space lies over the base. -/
theorem affineSpaceIsoOfSectionsIso_hom_over :
    (affineSpaceIsoOfSectionsIso π Φ hΦ).hom ≫ (𝔸(n; S) ↘ S) = π :=
  homOfVector_over π _

/-- The presentation of an affine scheme as affine space pulls the `i`-th coordinate back to the
`i`-th variable of the given polynomial presentation of its sections. -/
theorem affineSpaceIsoOfSectionsIso_hom_appTop_coord (i : n) :
    (affineSpaceIsoOfSectionsIso π Φ hΦ).hom.appTop (coord S i) = Φ.inv (MvPolynomial.X i) :=
  homOfVector_appTop_coord π _ i

end

/-! ### Sections of a restriction -/

/-- The sections of the restriction of a morphism to an open of the target and its inverse
image. -/
theorem morphismRestrict_appTop' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop = U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact (Scheme.Hom.resLE_app_top f _).trans (by rw [← Scheme.Hom.app_eq_appLE])

/-- The sections of a restriction, evaluated on the image of a section of the target open. -/
private theorem resLE_appTop_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.resLE U V e).appTop (U.topIso.inv x) = V.topIso.inv (f.appLE U V e x) := by
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.Hom.resLE_app_top f e))
    _).trans ?_
  exact congrArg (fun z => V.topIso.inv (f.appLE U V e z)) (Iso.inv_hom_id_apply U.topIso x)

/-- The sections of `f ∣_ U`, evaluated on the image of a section of `U`. -/
private theorem morphismRestrict_appTop_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv x) = (f ⁻¹ᵁ U).topIso.inv (f.app U x) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv, Scheme.Hom.app_eq_appLE]

/-- The inverse image of an open of the base in a fibre product may be taken along either
projection. -/
theorem preimage_pullback_fst_eq {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    (V : Y.Opens) :
    pullback.fst f₁ f₂ ⁻¹ᵁ (f₁ ⁻¹ᵁ V) = pullback.snd f₁ f₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

/-- **Over an open subscheme of the base, a fibre product of two morphisms is the fibre product
of their restrictions**, the second leg being the restriction of the second projection. -/
theorem isPullback_restrict_pullback {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    (V : Y.Opens) :
    IsPullback (pullback.fst f₁ f₂ ∣_ (f₁ ⁻¹ᵁ V))
      ((pullback.snd f₁ f₂).resLE (f₂ ⁻¹ᵁ V) (pullback.fst f₁ f₂ ⁻¹ᵁ (f₁ ⁻¹ᵁ V))
        (preimage_pullback_fst_eq f₁ f₂ V).le)
      (f₁ ∣_ V) (f₂ ∣_ V) := by
  have hb := Scheme.Hom.resLE_comp_ι (pullback.snd f₁ f₂)
    (U := f₂ ⁻¹ᵁ V) (V := pullback.fst f₁ f₂ ⁻¹ᵁ (f₁ ⁻¹ᵁ V))
    (preimage_pullback_fst_eq f₁ f₂ V).le
  have outer := (isPullback_morphismRestrict (pullback.fst f₁ f₂) (f₁ ⁻¹ᵁ V)).paste_vert
    (IsPullback.of_hasPullback f₁ f₂)
  rw [← morphismRestrict_ι f₁ V, ← hb] at outer
  refine IsPullback.of_bot outer ?_ (isPullback_morphismRestrict f₂ V)
  refine (cancel_mono V.ι).mp ?_
  rw [Category.assoc, Category.assoc, morphismRestrict_ι f₁ V, morphismRestrict_ι f₂ V,
    ← Category.assoc, ← Category.assoc, morphismRestrict_ι (pullback.fst f₁ f₂) (f₁ ⁻¹ᵁ V), hb,
    Category.assoc, Category.assoc, pullback.condition]

/-- **Over an open subscheme of the base, a fibre product of two morphisms is the fibre product of
their restrictions.** The second leg of the square is the one the universal property produces. -/
theorem exists_isPullback_morphismRestrict_pullback {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y)
    (f₂ : X₂ ⟶ Y) (V : Y.Opens) :
    ∃ b : (pullback.fst f₁ f₂ ⁻¹ᵁ (f₁ ⁻¹ᵁ V)).toScheme ⟶ (f₂ ⁻¹ᵁ V).toScheme,
      IsPullback (pullback.fst f₁ f₂ ∣_ (f₁ ⁻¹ᵁ V)) b (f₁ ∣_ V) (f₂ ∣_ V) :=
  ⟨_, isPullback_restrict_pullback f₁ f₂ V⟩

/-! ### Polynomial rings under renaming and change of coefficients -/

/-- A ring isomorphism, read as an isomorphism in `CommRingCat`. -/
def commRingCatIsoOfRingEquiv {A B : CommRingCat.{u}} (f : A ≃+* B) : A ≅ B where
  hom := CommRingCat.ofHom f.toRingHom
  inv := CommRingCat.ofHom f.symm.toRingHom
  hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ f.symm_apply_apply x)
  inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ f.apply_symm_apply x)

/-- A polynomial ring is carried to a polynomial ring by a renaming of the variables together
with an isomorphism of the coefficient ring. -/
def mvPolynomialRingEquiv {σ τ : Type*} (e : σ ≃ τ) {A B : Type*} [CommRing A] [CommRing B]
    (f : A ≃+* B) : MvPolynomial σ A ≃+* MvPolynomial τ B :=
  (MvPolynomial.mapEquiv σ f).trans (MvPolynomial.renameEquiv B e).toRingEquiv

/-- `mvPolynomialRingEquiv e f` carries the variable `X i` to the variable `X (e i)`. -/
theorem mvPolynomialRingEquiv_X {σ τ : Type*} (e : σ ≃ τ) {A B : Type*} [CommRing A] [CommRing B]
    (f : A ≃+* B) (i : σ) :
    mvPolynomialRingEquiv e f (MvPolynomial.X i) = MvPolynomial.X (e i) := by
  change MvPolynomial.rename e (MvPolynomial.map (f : A →+* B) (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X, MvPolynomial.rename_X]

/-- `mvPolynomialRingEquiv e f` carries the constant `C a` to the constant `C (f a)`. -/
theorem mvPolynomialRingEquiv_C {σ τ : Type*} (e : σ ≃ τ) {A B : Type*} [CommRing A] [CommRing B]
    (f : A ≃+* B) (a : A) :
    mvPolynomialRingEquiv e f (MvPolynomial.C a) = MvPolynomial.C (f a) := by
  change MvPolynomial.rename e (MvPolynomial.map (f : A →+* B) (MvPolynomial.C a)) = _
  rw [MvPolynomial.map_C, MvPolynomial.rename_C]
  rfl

/-- The inverse of `mvPolynomialRingEquiv e f` carries the variable `X j` to the variable
`X (e.symm j)`. -/
theorem mvPolynomialRingEquiv_symm_X {σ τ : Type*} (e : σ ≃ τ) {A B : Type*} [CommRing A]
    [CommRing B] (f : A ≃+* B) (j : τ) :
    (mvPolynomialRingEquiv e f).symm (MvPolynomial.X j) = MvPolynomial.X (e.symm j) := by
  rw [RingEquiv.symm_apply_eq, mvPolynomialRingEquiv_X, Equiv.apply_symm_apply]

/-- The inverse of `mvPolynomialRingEquiv e f` carries the constant `C x` to the constant
`C (f.symm x)`. -/
theorem mvPolynomialRingEquiv_symm_C {σ τ : Type*} (e : σ ≃ τ) {A B : Type*} [CommRing A]
    [CommRing B] (f : A ≃+* B) (x : B) :
    (mvPolynomialRingEquiv e f).symm (MvPolynomial.C x) = MvPolynomial.C (f.symm x) := by
  rw [RingEquiv.symm_apply_eq, mvPolynomialRingEquiv_C, RingEquiv.apply_symm_apply]

/-! ### A common trivializing affine open for two sheaves -/

/-- **Two finite locally free sheaves of rank `r` have free sections of rank `r` over small
enough common affine opens.** Around every point there is an affine open `V` on which both
`Γ(ℰ, V)` and `Γ(ℱ, V)` are free `Γ(X, V)`-modules with a basis indexed by `Fin r`. -/
theorem exists_isAffineOpen_basis_sections₂ {X : Scheme.{u}} (E F : X.Modules)
    [E.IsQuasicoherent] [F.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(E, V)) ∧
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(F, V)) := by
  have key : ∀ (G : X.Modules) [G.IsQuasicoherent]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r],
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → (V : Set X) ⊆ U →
        Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(G, V)) := by
    intro G _ _
    obtain ⟨U, hxU, ⟨e⟩⟩ := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf G r x
    refine ⟨U, hxU, fun V hV hVU ↦ ?_⟩
    have hr : Set.range hV.fromSpec.base ⊆ Set.range U.ι.base := by
      rwa [← Scheme.Hom.coe_opensRange, hV.opensRange_fromSpec, Scheme.Opens.range_ι]
    obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset U.ι hV.fromSpec G
      (ULift.{u} (Fin r)) hr e
    have hb := (tilde_fixed_free_iff_basis Γ(X, V) Γ(G, V) (ULift.{u} (Fin r))).mp
      ⟨Stacks.Modules.tildeIsoRestrictFromSpec G hV ≪≫ e'⟩
    exact hb.map fun b ↦ b.reindex Equiv.ulift
  obtain ⟨U₁, hxU₁, h₁⟩ := key E
  obtain ⟨U₂, hxU₂, h₂⟩ := key F
  obtain ⟨V, hV, hxV, hVU⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := U₁ ⊓ U₂) ⟨hxU₁, hxU₂⟩
  exact ⟨V, hV, hxV, h₁ V hV (hVU.trans Set.inter_subset_left),
    h₂ V hV (hVU.trans Set.inter_subset_right)⟩

/-! ### The chart of a relative spectrum over an affine open of the base -/

/-- **The sections of the relative spectrum of a quasi-coherent algebra over the inverse image of
an affine open of the base are the sections of the algebra over that open**, through the
universal map of [Stacks, Tag 01LX]. -/
def relativeSpecSectionsIso (s : Stacks.RelativeSpec.RelativeSpecSituation.{u})
    (U : s.base.affineOpens) :
    s.algebra.sections U.1 ≅
      Γ((Stacks.RelativeSpec.gluedSpectrum s).scheme,
        (Stacks.RelativeSpec.gluedSpectrum s).toBase ⁻¹ᵁ U.1) :=
  asIso ((Stacks.RelativeSpec.universalAlgebraMap s).right.app (op U.1))

/-- The chart of the relative spectrum carries the structure map of the algebra to the sections
of the structure morphism. -/
theorem relativeSpecSectionsIso_hom_comp (s : Stacks.RelativeSpec.RelativeSpecSituation.{u})
    (U : s.base.affineOpens) :
    s.algebra.hom.hom.app (op U.1) ≫ (relativeSpecSectionsIso s U).hom =
      (Stacks.RelativeSpec.gluedSpectrum s).toBase.app U.1 :=
  (Stacks.RelativeSpec.toBase_app s U.1).symm

/-- The chart of the relative spectrum carries the structure map of the algebra to the sections
of the structure morphism, read on elements. -/
theorem relativeSpecSectionsIso_hom_app (s : Stacks.RelativeSpec.RelativeSpecSituation.{u})
    (U : s.base.affineOpens) (r : Γ(s.base, U.1)) :
    (relativeSpecSectionsIso s U).hom ((s.algebra.hom.hom.app (op U.1)) r) =
      ((Stacks.RelativeSpec.gluedSpectrum s).toBase.app U.1) r :=
  DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (relativeSpecSectionsIso_hom_comp s U)) r

end Stacks.Chow

namespace Stacks.Chow.TensorZeroScheme

open Stacks.Chow Stacks.LineBundle

section OneBundle

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- The inverse of an invertible module is quasi-coherent. -/
instance isQuasicoherent_inverseModule (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    (inverseModule Y N).IsQuasicoherent :=
  Stacks.Divisors.isQuasicoherent_of_isInvertible (inverseModule Y N)

/-- The inverse of an invertible module is finite locally free of rank one. -/
instance isFiniteLocallyFreeOfRank_inverseModule (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (inverseModule Y N) 1 :=
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y (inverseModule Y N)

include hM in
/-- **The polynomial chart of the line bundle of an invertible module over an affine open of the
base trivializing the inverse module**: the sections of the line bundle over the inverse image
of `V` are a polynomial ring in one variable over `Γ(Y, V)`.

The chart is the identification of those sections with the sections of `Sym(M^{⊗ -1})` over `V`,
followed by the polynomial presentation
`Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv` of the latter attached to a basis of
`Γ(M^{⊗ -1}, V)`. -/
def lineBundleChartIso (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≅
      CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))) :=
  (relativeSpecSectionsIso (inverseSituation Y M).relativeSpecSituation V).symm ≪≫
    commRingCatIsoOfRingEquiv
      (A := (inverseSituation Y M).relativeSpecSituation.algebra.sections (V.1 : Y.Opens))
      (B := CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))))
      (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv
        (inverseModule Y M) V.2 b)

include hM in
/-- **The polynomial chart of a line bundle carries the structure morphism to the inclusion of
constants**, so it is an isomorphism of `Γ(Y, V)`-algebras. -/
theorem lineBundleChartIso_hom_comp (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    (lineBundleProj Y M).app (V.1 : Y.Opens) ≫ (lineBundleChartIso Y M V b).hom =
      CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := Γ(Y, (V.1 : Y.Opens)))) :=
  have step1 : (inverseSituation Y M).relativeSpecSituation.algebra.hom.hom.app
        (op (V.1 : Y.Opens)) ≫
      (relativeSpecSectionsIso (inverseSituation Y M).relativeSpecSituation V).hom =
      (lineBundleProj Y M).app (V.1 : Y.Opens) :=
    relativeSpecSectionsIso_hom_comp (inverseSituation Y M).relativeSpecSituation V
  have step2 : (lineBundleProj Y M).app (V.1 : Y.Opens) ≫
      (relativeSpecSectionsIso (inverseSituation Y M).relativeSpecSituation V).inv =
      (inverseSituation Y M).relativeSpecSituation.algebra.hom.hom.app (op (V.1 : Y.Opens)) :=
    (Iso.comp_inv_eq _).mpr step1.symm
  have step3 : (inverseSituation Y M).relativeSpecSituation.algebra.hom.hom.app
        (op (V.1 : Y.Opens)) ≫
      (commRingCatIsoOfRingEquiv
        (A := (inverseSituation Y M).relativeSpecSituation.algebra.sections (V.1 : Y.Opens))
        (B := CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))))
        (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv
          (inverseModule Y M) V.2 b)).hom =
      CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := Γ(Y, (V.1 : Y.Opens)))) :=
    CommRingCat.hom_ext (RingHom.ext fun r =>
      Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv_app (inverseModule Y M) V.2 b r)
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (commRingCatIsoOfRingEquiv
        (A := (inverseSituation Y M).relativeSpecSituation.algebra.sections (V.1 : Y.Opens))
        (B := CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))))
        (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv
          (inverseModule Y M) V.2 b)).hom) step2).trans step3)

include hM in
/-- The polynomial chart of a line bundle carries the structure morphism to the inclusion of
constants, read on elements. -/
theorem lineBundleChartIso_hom_app (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens)))
    (r : Γ(Y, (V.1 : Y.Opens))) :
    (lineBundleChartIso Y M V b).hom (((lineBundleProj Y M).app (V.1 : Y.Opens)) r) =
      MvPolynomial.C r :=
  DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (lineBundleChartIso_hom_comp Y M V b)) r

/-- The renaming of a polynomial ring over `Γ(Y, V)` in `Fin 1` variables into a polynomial ring
over the global sections of the open subscheme `V` in `ULift (Fin 1)` variables, which is the
index type of an affine line over `V`. -/
def factorPolyIso (V : Y.affineOpens) :
    CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ((V.1 : Y.Opens).toScheme, ⊤)) :=
  commRingCatIsoOfRingEquiv
    (mvPolynomialRingEquiv Equiv.ulift.symm
      ((V.1 : Y.Opens).topIso.commRingCatIsoToRingEquiv).symm)

include hM in
/-- **The polynomial chart of a line bundle, read on the global sections of the open subscheme
`q^{-1}(V)` and in the index type of an affine line over `V`.** -/
def factorSectionsIso (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    Γ((lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).toScheme, ⊤) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ((V.1 : Y.Opens).toScheme, ⊤)) :=
  (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).topIso ≪≫ lineBundleChartIso Y M V b ≪≫
    factorPolyIso Y V

include hM in
/-- The chart of a line bundle over the open subscheme `q^{-1}(V)` carries the structure morphism
to the inclusion of constants. -/
theorem factorSectionsIso_hom_comp (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    (lineBundleProj Y M ∣_ (V.1 : Y.Opens)).appTop ≫ (factorSectionsIso Y M V b).hom =
      CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin 1))
        (R := Γ((V.1 : Y.Opens).toScheme, ⊤))) := by
  have hC : CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := Γ(Y, (V.1 : Y.Opens)))) ≫
      (factorPolyIso Y V).hom =
      (V.1 : Y.Opens).topIso.inv ≫ CommRingCat.ofHom (MvPolynomial.C
        (σ := ULift.{u} (Fin 1)) (R := Γ((V.1 : Y.Opens).toScheme, ⊤))) :=
    CommRingCat.hom_ext (RingHom.ext fun r =>
      mvPolynomialRingEquiv_C Equiv.ulift.symm
        ((V.1 : Y.Opens).topIso.commRingCatIsoToRingEquiv).symm r)
  have hstep : (lineBundleProj Y M).app (V.1 : Y.Opens) ≫
      ((lineBundleChartIso Y M V b).hom ≫ (factorPolyIso Y V).hom) =
      (V.1 : Y.Opens).topIso.inv ≫ CommRingCat.ofHom (MvPolynomial.C
        (σ := ULift.{u} (Fin 1)) (R := Γ((V.1 : Y.Opens).toScheme, ⊤))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (factorPolyIso Y V).hom)
        (lineBundleChartIso_hom_comp Y M V b)).trans hC)
  change (lineBundleProj Y M ∣_ (V.1 : Y.Opens)).appTop ≫
      (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).topIso.hom ≫
        ((lineBundleChartIso Y M V b).hom ≫ (factorPolyIso Y V).hom) = _
  rw [morphismRestrict_appTop', Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hstep]
  exact Iso.hom_inv_id_assoc _ _

include hM in
/-- The chart of a line bundle over the open subscheme `q^{-1}(V)` carries the `i`-th variable to
the `i`-th variable of the chart over `V`. -/
theorem factorSectionsIso_inv_X (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens)))
    (i : Fin 1) :
    (factorSectionsIso Y M V b).inv (MvPolynomial.X (ULift.up i)) =
      (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).topIso.inv
        ((lineBundleChartIso Y M V b).inv (MvPolynomial.X i)) := by
  change (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).topIso.inv
      ((lineBundleChartIso Y M V b).inv ((factorPolyIso Y V).inv
        (MvPolynomial.X (ULift.up i)))) = _
  congr 2
  exact mvPolynomialRingEquiv_symm_X Equiv.ulift.symm
    ((V.1 : Y.Opens).topIso.commRingCatIsoToRingEquiv).symm (ULift.up i)

include hM in
/-- **The line bundle of an invertible module, over an affine open of the base trivializing the
inverse module, is the affine line over that open** — with the first coordinate the variable of
the polynomial chart. -/
def lineBundleAffineLineIso (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).toScheme ≅
      𝔸(ULift.{u} (Fin 1); (V.1 : Y.Opens).toScheme) :=
  haveI : IsAffine (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).toScheme :=
    Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y M V
  haveI : IsAffine (V.1 : Y.Opens).toScheme := V.2
  affineSpaceIsoOfSectionsIso (lineBundleProj Y M ∣_ (V.1 : Y.Opens))
    (factorSectionsIso Y M V b) (factorSectionsIso_hom_comp Y M V b)

include hM in
/-- The presentation of a line bundle as an affine line lies over the base. -/
theorem lineBundleAffineLineIso_hom_over (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    (lineBundleAffineLineIso Y M V b).hom ≫
        (𝔸(ULift.{u} (Fin 1); (V.1 : Y.Opens).toScheme) ↘ (V.1 : Y.Opens).toScheme) =
      lineBundleProj Y M ∣_ (V.1 : Y.Opens) :=
  have : IsAffine (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).toScheme :=
    Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y M V
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  affineSpaceIsoOfSectionsIso_hom_over _ _ _

include hM in
/-- The presentation of a line bundle as an affine line pulls the coordinate back to the variable
of the polynomial chart. -/
theorem lineBundleAffineLineIso_hom_appTop_coord (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens)))
    (i : Fin 1) :
    (lineBundleAffineLineIso Y M V b).hom.appTop
        (AffineSpace.coord (V.1 : Y.Opens).toScheme (ULift.up i)) =
      (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).topIso.inv
        ((lineBundleChartIso Y M V b).inv (MvPolynomial.X i)) :=
  have : IsAffine (lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)).toScheme :=
    Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y M V
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  (affineSpaceIsoOfSectionsIso_hom_appTop_coord _ _ _ (ULift.up i)).trans
    (factorSectionsIso_inv_X Y M V b i)

include hM in
/-- **The polynomial chart of the line bundle of an invertible module over an affine open of the
base trivializing the inverse module**, as a ring isomorphism. -/
def lineBundleChart (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens))) :
    Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
      MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens)) :=
  (lineBundleChartIso Y M V b).commRingCatIsoToRingEquiv

include hM in
/-- The polynomial chart of a line bundle carries the structure morphism to the inclusion of
constants. -/
theorem lineBundleChart_app (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens)))
    (r : Γ(Y, (V.1 : Y.Opens))) :
    lineBundleChart Y M V b (((lineBundleProj Y M).app (V.1 : Y.Opens)) r) =
      MvPolynomial.C r :=
  lineBundleChartIso_hom_app Y M V b r

include hM in
/-- The variable of the polynomial chart of a line bundle, read through the ring isomorphism. -/
theorem lineBundleChart_symm_X (V : Y.affineOpens)
    (b : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y M, (V.1 : Y.Opens)))
    (i : Fin 1) :
    (lineBundleChart Y M V b).symm (MvPolynomial.X i) =
      (lineBundleChartIso Y M V b).inv (MvPolynomial.X i) :=
  rfl

end OneBundle

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-! ### The polynomial chart of the ambient space -/

section Ambient

variable (V : Y.affineOpens)
  (b₁ : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y L₁, (V.1 : Y.Opens)))
  (b₂ : Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens)) Γ(inverseModule Y L₂, (V.1 : Y.Opens)))

/-- The index type of the fibre product of two affine lines, renamed to `Fin 2`. -/
def sumUliftFinTwoEquiv : ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin 1) ≃ Fin 2 :=
  (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans finSumFinEquiv

/-- The first summand is the variable `0`. -/
theorem sumUliftFinTwoEquiv_inl : sumUliftFinTwoEquiv.{u} (Sum.inl (ULift.up 0)) = 0 := rfl

/-- The second summand is the variable `1`. -/
theorem sumUliftFinTwoEquiv_inr : sumUliftFinTwoEquiv.{u} (Sum.inr (ULift.up 0)) = 1 := rfl

include h₁ h₂ in
/-- **The ambient space of [Stacks, Tag 0F97] is affine two-space over an affine open of the base
trivializing both inverse modules.** -/
def ambientSpaceIso : (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)).toScheme ≅
    𝔸(ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin 1); (V.1 : Y.Opens).toScheme) :=
  pullbackAffineSpaceSumIso
    (isPullback_restrict_pullback (lineBundleProj Y L₁) (lineBundleProj Y L₂) (V.1 : Y.Opens))
    (lineBundleAffineLineIso_hom_over Y L₁ V b₁) (lineBundleAffineLineIso_hom_over Y L₂ V b₂)

include h₁ h₂ b₁ b₂ in
/-- **The inverse image of an affine open of the base in the ambient space of [Stacks, Tag 0F97]
is affine.** -/
theorem isAffineOpen_totalProj_preimage :
    IsAffineOpen (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) :=
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  IsAffine.of_isIso (ambientSpaceIso Y L₁ L₂ V b₁ b₂).hom

include h₁ h₂ in
/-- The comparison of the ambient space with affine two-space carries the coordinate of the first
summand to the fibre coordinate of the first factor. -/
theorem ambientSpaceIso_hom_appTop_coord_inl (i : ULift.{u} (Fin 1)) :
    (ambientSpaceIso Y L₁ L₂ V b₁ b₂).hom.appTop
        (AffineSpace.coord (V.1 : Y.Opens).toScheme (Sum.inl i)) =
      (firstProj Y L₁ L₂ ∣_ (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))).appTop
        ((lineBundleAffineLineIso Y L₁ V b₁).hom.appTop
          (AffineSpace.coord (V.1 : Y.Opens).toScheme i)) :=
  pullbackAffineSpaceSumIso_hom_appTop_coord_inl _ (lineBundleAffineLineIso_hom_over Y L₁ V b₁)
    (lineBundleAffineLineIso_hom_over Y L₂ V b₂) i

include h₁ h₂ in
/-- The comparison of the ambient space with affine two-space carries the coordinate of the second
summand to the fibre coordinate of the second factor. -/
theorem ambientSpaceIso_hom_appTop_coord_inr (j : ULift.{u} (Fin 1)) :
    (ambientSpaceIso Y L₁ L₂ V b₁ b₂).hom.appTop
        (AffineSpace.coord (V.1 : Y.Opens).toScheme (Sum.inr j)) =
      ((secondProj Y L₁ L₂).resLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (preimage_pullback_fst_eq (lineBundleProj Y L₁) (lineBundleProj Y L₂)
            (V.1 : Y.Opens)).le).appTop
        ((lineBundleAffineLineIso Y L₂ V b₂).hom.appTop
          (AffineSpace.coord (V.1 : Y.Opens).toScheme j)) :=
  pullbackAffineSpaceSumIso_hom_appTop_coord_inr _ (lineBundleAffineLineIso_hom_over Y L₁ V b₁)
    (lineBundleAffineLineIso_hom_over Y L₂ V b₂) j

include h₁ h₂ in
/-- The comparison of the ambient space with affine two-space lies over the base. -/
theorem ambientSpaceIso_hom_over :
    (ambientSpaceIso Y L₁ L₂ V b₁ b₂).hom ≫
        (𝔸(ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin 1); (V.1 : Y.Opens).toScheme) ↘
          (V.1 : Y.Opens).toScheme) =
      totalProj Y L₁ L₂ ∣_ (V.1 : Y.Opens) :=
  (pullbackAffineSpaceSumIso_hom_over _ (lineBundleAffineLineIso_hom_over Y L₁ V b₁)
    (lineBundleAffineLineIso_hom_over Y L₂ V b₂)).trans
    (morphismRestrict_comp (firstProj Y L₁ L₂) (lineBundleProj Y L₁) (V.1 : Y.Opens)).symm

/-- The renaming of the polynomial ring in the two coordinates of the fibre product into the
polynomial ring in `Fin 2` variables over `Γ(Y, V)`. -/
def ambientPolyIso :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin 1))
        Γ((V.1 : Y.Opens).toScheme, ⊤)) ≅
      CommRingCat.of (MvPolynomial (Fin 2) Γ(Y, (V.1 : Y.Opens))) :=
  commRingCatIsoOfRingEquiv
    (mvPolynomialRingEquiv sumUliftFinTwoEquiv
      (V.1 : Y.Opens).topIso.commRingCatIsoToRingEquiv)

include h₁ h₂ in
/-- **The polynomial chart of the ambient space of [Stacks, Tag 0F97]**: over an affine open `V`
of the base trivializing both inverse modules, the sections of the ambient space over
`q^{-1}(V)` form a polynomial ring in two variables over `Γ(Y, V)`. -/
def ambientChart :
    Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
      MvPolynomial (Fin 2) Γ(Y, (V.1 : Y.Opens)) :=
  haveI : IsAffine (V.1 : Y.Opens).toScheme := V.2
  ((totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)).topIso.symm ≪≫
    affineSpaceChartIso (ambientSpaceIso Y L₁ L₂ V b₁ b₂) ≪≫
      ambientPolyIso Y V).commRingCatIsoToRingEquiv

/-- An element of the sections of the ambient space is the image of a polynomial under the inverse
of the chart as soon as its inverse image under the comparison with affine space is. -/
private theorem ambientChart_symm_eq (p : MvPolynomial (Fin 2) Γ(Y, (V.1 : Y.Opens)))
    (q : MvPolynomial (ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin 1)) Γ((V.1 : Y.Opens).toScheme, ⊤))
    (z : Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)))
    (hq : (ambientPolyIso Y V).inv p = q)
    (hz : (affineSpaceChartIso (ambientSpaceIso Y L₁ L₂ V b₁ b₂)).inv q =
      (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)).topIso.inv z) :
    (ambientChart Y L₁ L₂ V b₁ b₂).symm p = z := by
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  change (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)).topIso.hom
    ((affineSpaceChartIso (ambientSpaceIso Y L₁ L₂ V b₁ b₂)).inv ((ambientPolyIso Y V).inv p)) = z
  rw [hq, hz, Iso.inv_hom_id_apply]

include h₁ h₂ in
/-- **The polynomial chart of the ambient space carries the structure morphism to the inclusion
of constants**, so it is an isomorphism of `Γ(Y, V)`-algebras. -/
theorem ambientChart_symm_C (r : Γ(Y, (V.1 : Y.Opens))) :
    (ambientChart Y L₁ L₂ V b₁ b₂).symm (MvPolynomial.C r) =
      ((totalProj Y L₁ L₂).app (V.1 : Y.Opens)) r := by
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  exact ambientChart_symm_eq Y L₁ L₂ V b₁ b₂ _ _ _ (mvPolynomialRingEquiv_symm_C _ _ r)
    ((affineSpaceChartIso_inv_C _ (ambientSpaceIso_hom_over Y L₁ L₂ V b₁ b₂) _).trans
      (morphismRestrict_appTop_topIso_inv _ _ _))

include h₁ h₂ in
/-- **The first variable of the polynomial chart of the ambient space is the fibre coordinate of
the first factor**: it is the restriction along the first projection of the variable of the
polynomial chart of the first line bundle. -/
theorem ambientChart_symm_X_zero :
    (ambientChart Y L₁ L₂ V b₁ b₂).symm (MvPolynomial.X 0) =
      ((firstProj Y L₁ L₂).app (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)))
        ((lineBundleChartIso Y L₁ V b₁).inv (MvPolynomial.X 0)) := by
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  exact ambientChart_symm_eq Y L₁ L₂ V b₁ b₂ _ _ _
    ((mvPolynomialRingEquiv_symm_X _ _ _).trans
      (congrArg MvPolynomial.X ((Equiv.symm_apply_eq _).mpr sumUliftFinTwoEquiv_inl.symm)))
    ((affineSpaceChartIso_inv_X _ _).trans
      ((ambientSpaceIso_hom_appTop_coord_inl Y L₁ L₂ V b₁ b₂ (ULift.up 0)).trans
        ((congrArg (firstProj Y L₁ L₂ ∣_ (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))).appTop
          (lineBundleAffineLineIso_hom_appTop_coord Y L₁ V b₁ 0)).trans
          (morphismRestrict_appTop_topIso_inv _ _ _))))

include h₁ h₂ in
/-- **The second variable of the polynomial chart of the ambient space is the fibre coordinate of
the second factor**: it is the restriction along the second projection of the variable of the
polynomial chart of the second line bundle. -/
theorem ambientChart_symm_X_one :
    (ambientChart Y L₁ L₂ V b₁ b₂).symm (MvPolynomial.X 1) =
      ((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (preimage_pullback_fst_eq (lineBundleProj Y L₁) (lineBundleProj Y L₂)
            (V.1 : Y.Opens)).le)
        ((lineBundleChartIso Y L₂ V b₂).inv (MvPolynomial.X 0)) := by
  have : IsAffine (V.1 : Y.Opens).toScheme := V.2
  exact ambientChart_symm_eq Y L₁ L₂ V b₁ b₂ _ _ _
    ((mvPolynomialRingEquiv_symm_X _ _ _).trans
      (congrArg MvPolynomial.X ((Equiv.symm_apply_eq _).mpr sumUliftFinTwoEquiv_inr.symm)))
    ((affineSpaceChartIso_inv_X _ _).trans
      ((ambientSpaceIso_hom_appTop_coord_inr Y L₁ L₂ V b₁ b₂ (ULift.up 0)).trans
        ((congrArg ((secondProj Y L₁ L₂).resLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
            (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
            (preimage_pullback_fst_eq (lineBundleProj Y L₁) (lineBundleProj Y L₂)
              (V.1 : Y.Opens)).le).appTop
          (lineBundleAffineLineIso_hom_appTop_coord Y L₂ V b₂ 0)).trans
          (resLE_appTop_topIso_inv _ _ _))))

include h₁ h₂ in
/-- **The polynomial chart of the ambient space carries the structure morphism to the inclusion
of constants.** -/
theorem ambientChart_app (r : Γ(Y, (V.1 : Y.Opens))) :
    ambientChart Y L₁ L₂ V b₁ b₂ (((totalProj Y L₁ L₂).app (V.1 : Y.Opens)) r) =
      MvPolynomial.C r :=
  (RingEquiv.eq_symm_apply _).mp (ambientChart_symm_C Y L₁ L₂ V b₁ b₂ r).symm

include h₁ h₂ in
/-- **The variable of the polynomial chart of the first line bundle becomes the first variable of
the polynomial chart of the ambient space**, under restriction along the first projection. -/
theorem ambientChart_app_firstProj
    (t : Γ(lineBundleSpace Y L₁, lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)))
    (ht : lineBundleChart Y L₁ V b₁ t = MvPolynomial.X 0) :
    ambientChart Y L₁ L₂ V b₁ b₂
        (((firstProj Y L₁ L₂).app (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))) t) =
      MvPolynomial.X 0 :=
  have ht' : t = (lineBundleChartIso Y L₁ V b₁).inv (MvPolynomial.X 0) :=
    (RingEquiv.eq_symm_apply _).mpr ht
  (RingEquiv.eq_symm_apply _).mp
    ((congrArg ((firstProj Y L₁ L₂).app (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))) ht').trans
      (ambientChart_symm_X_zero Y L₁ L₂ V b₁ b₂).symm)

include h₁ h₂ in
/-- **The variable of the polynomial chart of the second line bundle becomes the second variable
of the polynomial chart of the ambient space**, under restriction along the second
projection. -/
theorem ambientChart_app_secondProj
    (t : Γ(lineBundleSpace Y L₂, lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)))
    (ht : lineBundleChart Y L₂ V b₂ t = MvPolynomial.X 0) :
    ambientChart Y L₁ L₂ V b₁ b₂
        (((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
            (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
            (preimage_pullback_fst_eq (lineBundleProj Y L₁) (lineBundleProj Y L₂)
              (V.1 : Y.Opens)).le) t) =
      MvPolynomial.X 1 :=
  have ht' : t = (lineBundleChartIso Y L₂ V b₂).inv (MvPolynomial.X 0) :=
    (RingEquiv.eq_symm_apply _).mpr ht
  (RingEquiv.eq_symm_apply _).mp
    ((congrArg ((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (preimage_pullback_fst_eq (lineBundleProj Y L₁) (lineBundleProj Y L₂)
          (V.1 : Y.Opens)).le) ht').trans
      (ambientChart_symm_X_one Y L₁ L₂ V b₁ b₂).symm)

end Ambient

include h₁ h₂ in
/-- **Around every point of the base there is an affine open trivializing both inverse
modules**, which is where the polynomial chart of the ambient space lives. -/
theorem exists_affineOpen_basis_inverseModule (y : Y) :
    ∃ V : Y.affineOpens, y ∈ (V.1 : Y.Opens) ∧
      Nonempty (Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens))
        Γ(inverseModule Y L₁, (V.1 : Y.Opens))) ∧
      Nonempty (Module.Basis (Fin 1) Γ(Y, (V.1 : Y.Opens))
        Γ(inverseModule Y L₂, (V.1 : Y.Opens))) := by
  obtain ⟨V, hV, hyV, hb₁, hb₂⟩ :=
    Stacks.Chow.exists_isAffineOpen_basis_sections₂ (inverseModule Y L₁) (inverseModule Y L₂) 1 y
  exact ⟨⟨V, hV⟩, hyV, hb₁, hb₂⟩

include h₁ h₂ in
/-- **The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` of the ambient space of
[Stacks, Tag 0F97] is an affine-space bundle of rank two.** Each of the two line bundles is an
affine-space bundle of rank one; over the intersection of two trivializing opens both are
globally trivial, and there the restriction of `q` is the fibre product of the two restrictions,
hence the projection of affine two-space. -/
theorem isAffineSpaceBundle_totalProj :
    Stacks.Chow.IsAffineSpaceBundle (totalProj Y L₁ L₂) 2 := by
  intro y
  obtain ⟨U₁, hyU₁, htriv₁⟩ := Stacks.LineBundle.isAffineSpaceBundle_lineBundleProj Y L₁ y
  obtain ⟨U₂, hyU₂, htriv₂⟩ := Stacks.LineBundle.isAffineSpaceBundle_lineBundleProj Y L₂ y
  refine ⟨U₁ ⊓ U₂, ⟨hyU₁, hyU₂⟩, ?_⟩
  have hV₁ : IsTrivialAffineSpaceBundle (lineBundleProj Y L₁ ∣_ (U₁ ⊓ U₂)) 1 :=
    isTrivialAffineSpaceBundle_morphismRestrict_of_le _ inf_le_left 1 htriv₁
  have hV₂ : IsTrivialAffineSpaceBundle (lineBundleProj Y L₂ ∣_ (U₁ ⊓ U₂)) 1 :=
    isTrivialAffineSpaceBundle_morphismRestrict_of_le _ inf_le_right 1 htriv₂
  obtain ⟨b, hsq⟩ := exists_isPullback_morphismRestrict_pullback (lineBundleProj Y L₁)
    (lineBundleProj Y L₂) (U₁ ⊓ U₂)
  have key := isTrivialAffineSpaceBundle_fst_comp hsq 1 1 hV₁ hV₂
  rw [← morphismRestrict_comp] at key
  exact key

end Stacks.Chow.TensorZeroScheme

end
