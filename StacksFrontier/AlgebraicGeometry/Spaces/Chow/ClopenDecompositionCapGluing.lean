module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# Cap operations glued along a decomposition into open and closed subspaces

In Situation 0EDT let `X/B` be good and let `X = ∐_i X_i` be a decomposition of `X` into open and
closed subspaces. A good test space `g : X' ⟶ X` inherits the decomposition `X' = ∐_i X'_i`,
`X'_i = g^{-1}(X_i)`, and `CH_k(X') = ∏_i CH_k(X'_i)`
(`AlgebraicGeometry.Space.chowGroupCanonicalDecompositionEquiv`). Given, for every piece `X_i`,
additive maps `c_i ∩ - : CH_k(Y) ⟶ CH_{k-p}(Y)` on the good test spaces `Y ⟶ X_i`, the maps on the
test spaces of `X` which preserve these product decompositions and act by `c_i ∩ -` on the factors
are

`c ∩ α = (c_i ∩ α|_{X'_i})_i ∈ ∏_i CH_{k-p}(X'_i) = CH_{k-p}(X')`.

This is how Stacks 0ES2 defines the Chern classes of a finite locally free module of non-constant
rank. If every `c_i ∩ -` commutes with proper pushforward, flat pullback and the Gysin maps of
sections of invertible modules, so does `c ∩ -`: restriction to a piece commutes with each of the
three operations, by Stacks 0EPD for proper pushforward, by Stacks 0EPA for flat pullback and by
Stacks 0ER6 for the Gysin maps, the vanishing locus of the restricted section being the piece of
the vanishing locus.

## Main definitions

* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.preimage`: the decomposition of a good
  test space.
* `AlgebraicGeometry.Space.clopenGluedCap`: the glued maps `c ∩ -`.

## Main results

* `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict_clopenGluedCap`: `c ∩ -` acts by
  `c_i ∩ -` on the factor of `X'_i`.
* `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict_properPushforward`,
  `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict_flatPullback` and
  `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict_sectionGysinChowGroupMap`: restriction
  to a piece commutes with proper pushforward, flat pullback and the Gysin maps.
* `AlgebraicGeometry.Space.clopenGluedCap_properPushforward`,
  `AlgebraicGeometry.Space.clopenGluedCap_flatPullback` and
  `AlgebraicGeometry.Space.clopenGluedCap_sectionGysinChowGroupMap`: `c ∩ -` commutes with the
  three operations when every `c_i ∩ -` does.

## Implementation notes

The piece `X'_i` of a test space is the inverse image subfunctor `g^{-1}(X_i)` and the test space
structure of `X'_i` over `X_i` is `CategoryTheory.Subfunctor.fromPreimage`; its composite with
the inclusion of `X_i` is, definitionally, the inclusion of `X'_i` followed by `g`, so the Chow
groups of `X'_i` as a piece of `X'` and as a test space over `X_i` are the same groups. For the
Gysin maps the vanishing locus `Z(t|_{X'_i})` of the restricted section and the piece `Z(t)_i` of
the vanishing locus are two fibre products of the same cospan, and they are compared along the
canonical isomorphism, which is flat of relative dimension `0`.

## References

* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Two composites of flat pullbacks along equal composites -/

section FlatComposite

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y₁ Y₂ Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY₁ : Y₁ ⟶ D.space) (hY₁ : D.IsGood sY₁)
    (sY₂ : Y₂ ⟶ D.space) (hY₂ : D.IsGood sY₂) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)

/-- **A composite of two flat pullbacks is the flat pullback along the composite**, on
coefficient families, whatever the degrees in which the three maps are read. -/
theorem coe_flatPullbackMap_flatPullbackMap_of_comp_eq (f : X ⟶ Y₁) (g : Y₁ ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) (hf : f ≫ sY₁ = sX) (hg : g ≫ sZ = sY₁) (hh : h ≫ sZ = sX)
    (r s t : ℕ) (hrst : r + s = t) (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgs : HasRelativeDimension s D.site D.base D.base_mem g)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hht : HasRelativeDimension t D.site D.base D.base_mem h) (k m n n' : ℤ)
    (hm : k + (s : ℤ) = m) (hn : m + (r : ℤ) = n) (hn' : k + (t : ℤ) = n')
    (α : CycleGroup D sZ k) :
    (flatPullbackMap D sX hX sY₁ hY₁ f hf r hff hfr m n hn
        (flatPullbackMap D sY₁ hY₁ sZ hZ g hg s hgf hgs k m hm α)).1 =
      (flatPullbackMap D sX hX sZ hZ h hh t hhf hht k n' hn' α).1 := by
  subst hm
  have e := congrArg (fun φ => (φ α).1)
    (flatPullbackMap_comp D sX hX sY₁ hY₁ sZ hZ f g hf hg r s hff hfr hgf hgs k n
      (by push_cast; omega))
  simp only [AddMonoidHom.comp_apply] at e
  rw [← e]
  exact flatPullbackMap_coe_congr D sX hX sZ hZ hfg _ hh (by omega) _ hhf _ hht k n k n' _ hn' α
    α rfl

/-- **Two composites of flat pullbacks along equal composite morphisms agree**, on coefficient
families: `f₁^* g₁^* = f₂^* g₂^*` when `f₁ ≫ g₁ = f₂ ≫ g₂` with the same total relative
dimension. -/
theorem coe_flatPullbackMap_flatPullbackMap_of_comp_eq_comp (f₁ : X ⟶ Y₁) (g₁ : Y₁ ⟶ Z)
    (f₂ : X ⟶ Y₂) (g₂ : Y₂ ⟶ Z) (hcomm : f₁ ≫ g₁ = f₂ ≫ g₂) (hf₁ : f₁ ≫ sY₁ = sX)
    (hg₁ : g₁ ≫ sZ = sY₁) (hf₂ : f₂ ≫ sY₂ = sX) (hg₂ : g₂ ≫ sZ = sY₂) (r₁ s₁ r₂ s₂ : ℕ)
    (hrs : r₁ + s₁ = r₂ + s₂) (hff₁ : IsFlat D.site D.base D.base_mem f₁)
    (hfr₁ : HasRelativeDimension r₁ D.site D.base D.base_mem f₁)
    (hgf₁ : IsFlat D.site D.base D.base_mem g₁)
    (hgs₁ : HasRelativeDimension s₁ D.site D.base D.base_mem g₁)
    (hff₂ : IsFlat D.site D.base D.base_mem f₂)
    (hfr₂ : HasRelativeDimension r₂ D.site D.base D.base_mem f₂)
    (hgf₂ : IsFlat D.site D.base D.base_mem g₂)
    (hgs₂ : HasRelativeDimension s₂ D.site D.base D.base_mem g₂) (k m₁ n₁ m₂ n₂ : ℤ)
    (hm₁ : k + (s₁ : ℤ) = m₁) (hn₁ : m₁ + (r₁ : ℤ) = n₁) (hm₂ : k + (s₂ : ℤ) = m₂)
    (hn₂ : m₂ + (r₂ : ℤ) = n₂) (α : CycleGroup D sZ k) :
    (flatPullbackMap D sX hX sY₁ hY₁ f₁ hf₁ r₁ hff₁ hfr₁ m₁ n₁ hn₁
        (flatPullbackMap D sY₁ hY₁ sZ hZ g₁ hg₁ s₁ hgf₁ hgs₁ k m₁ hm₁ α)).1 =
      (flatPullbackMap D sX hX sY₂ hY₂ f₂ hf₂ r₂ hff₂ hfr₂ m₂ n₂ hn₂
        (flatPullbackMap D sY₂ hY₂ sZ hZ g₂ hg₂ s₂ hgf₂ hgs₂ k m₂ hm₂ α)).1 := by
  have hc := isFlat_and_hasRelativeDimension_comp D sX hX sY₁ hY₁ sZ hZ f₁ g₁ hf₁ hg₁ r₁ s₁
    hff₁ hfr₁ hgf₁ hgs₁
  rw [coe_flatPullbackMap_flatPullbackMap_of_comp_eq D sX hX sY₁ hY₁ sZ hZ f₁ g₁ (f₁ ≫ g₁) rfl
      hf₁ hg₁ (comp_structureMorphism_eq D sX sY₁ sZ f₁ g₁ hf₁ hg₁) r₁ s₁ (r₁ + s₁) rfl hff₁ hfr₁
      hgf₁ hgs₁ hc.2.1 hc.2.2 k m₁ n₁ n₁ hm₁ hn₁ (by push_cast; omega) α,
    coe_flatPullbackMap_flatPullbackMap_of_comp_eq D sX hX sY₂ hY₂ sZ hZ f₂ g₂ (f₁ ≫ g₁)
      hcomm.symm hf₂ hg₂ (comp_structureMorphism_eq D sX sY₁ sZ f₁ g₁ hf₁ hg₁) r₂ s₂ (r₁ + s₁)
      hrs.symm hff₂ hfr₂ hgf₂ hgs₂ hc.2.1 hc.2.2 k m₂ n₂ n₁ hm₂ hn₂ (by push_cast; omega) α]

end FlatComposite

/-! ### Cap families commuting with flat pullback, along equal test morphisms -/

section CapFamily

variable (D : BaseSpaceDimensionSituation.{u}) {W : D.Ambient} (sW : W ⟶ D.space) (p : ℤ)
    (c : ∀ {Y : D.Ambient} (g : Y ⟶ W) (hY : D.IsGood (g ≫ sW)) (k : ℤ),
      chowGroupCanonical.{u + 1} D (g ≫ sW) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ sW) hY (k - p))

include sW in
/-- **A cap family commuting with flat pullback commutes with it along any presentation**: when
`h ≫ g₁ = g₂` and the degrees are read through arbitrary equalities, the flat pullback axiom
still holds. -/
theorem cap_flatPullbackChowMapCanonical_of_comp_eq
    (hflat : ∀ {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ W) (hY₁ : D.IsGood (g ≫ sW)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ sW)) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
      (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ sW) hY₁ k),
      c (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g sW).symm m hhf hhr k (k + m) rfl α) =
        flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sW).symm m hhf
          hhr (k - p) (k + m - p) (by ring) (c g hY₁ k α))
    {Y₁ Y₂ : D.Ambient} (g₁ : Y₁ ⟶ W) (hY₁ : D.IsGood (g₁ ≫ sW)) (g₂ : Y₂ ⟶ W)
    (hY₂ : D.IsGood (g₂ ≫ sW)) (h : Y₂ ⟶ Y₁) (hhg : h ≫ g₁ = g₂) (hbase : h ≫ g₁ ≫ sW = g₂ ≫ sW)
    (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k n : ℤ) (hkn : k + m = n)
    (hkn' : k - p + m = n - p) (α : chowGroupCanonical.{u + 1} D (g₁ ≫ sW) hY₁ k) :
    c g₂ hY₂ n (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h hbase m hhf hhr k n hkn α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h hbase m hhf hhr (k - p) (n - p) hkn'
        (c g₁ hY₁ k α) := by
  subst hhg hkn
  exact hflat g₁ hY₁ h hY₂ m hhf hhr k α

end CapFamily

/-! ### The decomposition of a test space and restriction to its pieces -/

section Restriction

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
    {I : Type u} {V : I → Subfunctor X}

/-- **The decomposition of a good test space.** A decomposition `X = ∐_i X_i` into open and
closed subspaces pulls back to the decomposition `X' = ∐_i g^{-1}(X_i)` of a good `g : X' ⟶ X`. -/
theorem IsClopenSubspaceDecomposition.preimage
    (hV : IsClopenSubspaceDecomposition D sX fun i => (V i).ι) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    IsClopenSubspaceDecomposition D (g ≫ sX) fun i => ((V i).preimage g).ι :=
  isClopenSubspaceDecomposition_preimage g hV hY fun i =>
    isGood_ι_of_isOpenSubspace D (g ≫ sX) hY _
      (isOpenSubspace_preimage D.site D.base D.base_mem g (V i) hV.isGood.1 hY.1
        (hV.isOpenSubspace i))

variable (hV : IsClopenSubspaceDecomposition D sX fun i => (V i).ι)

include hV in
/-- The base change `g^{-1}(X_i) ⟶ g'^{-1}(X_i)` of a proper `h : Y₂ ⟶ Y₁`, `g' = h ≫ g`, is
proper. -/
theorem isProper_fromPreimage_preimage {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (i : I) :
    IsProper D.site D.base D.base_mem (((V i).preimage g).fromPreimage h) :=
  isProper_of_isPullback D.site D.base D.base_mem ((hV.preimage (h ≫ g) hY₂).isGoodPiece i).1
    hY₂.1 ((hV.preimage g hY₁).isGoodPiece i).1 hY₁.1
    (Subfunctor.isPullback_preimage h ((V i).preimage g)).flip hh

include hV in
/-- The base change `g'^{-1}(X_i) ⟶ g^{-1}(X_i)` of a flat `h : Y₂ ⟶ Y₁` of relative dimension
`m` is flat of relative dimension `m`. -/
theorem isFlat_and_hasRelativeDimension_fromPreimage_preimage {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (i : I) :
    IsFlat D.site D.base D.base_mem (((V i).preimage g).fromPreimage h) ∧
      HasRelativeDimension m D.site D.base D.base_mem (((V i).preimage g).fromPreimage h) :=
  have H := isFlat_and_hasRelativeDimension_of_isPullback D
    (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
    (((V i).preimage g).ι ≫ g ≫ sX) ((hV.preimage g hY₁).isGoodPiece i) ((h ≫ g) ≫ sX) hY₂
    (g ≫ sX) hY₁ rfl (Category.assoc h g sX).symm
    (Subfunctor.isPullback_preimage h ((V i).preimage g)) m hhf hhr
  ⟨H.2.1, H.2.2⟩

/-- **Restriction to a piece commutes with proper pushforward** (Stacks 0EPD): for a proper
`h : Y₂ ⟶ Y₁`, `(h_*α)|_{Y₁,i} = (h_i)_*(α|_{Y₂,i})`. -/
theorem chowGroupCanonicalPieceRestrict_properPushforward {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (i : I) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    chowGroupCanonicalPieceRestrict (hV.preimage g hY₁) i k
        (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh
          k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D
        (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
        (((V i).preimage g).ι ≫ g ≫ sX) ((hV.preimage g hY₁).isGoodPiece i)
        (p := ((V i).preimage g).fromPreimage h) rfl
        (isProper_fromPreimage_preimage hV g hY₁ h hY₂ hh i) k
        (chowGroupCanonicalPieceRestrict (hV.preimage (h ≫ g) hY₂) i k α) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  exact congrArg (chowClassCanonical.{u + 1} D (((V i).preimage g).ι ≫ g ≫ sX)
      ((hV.preimage g hY₁).isGoodPiece i) k)
    (flatPullback_properPushforward_unconditional D
      (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
      ((h ≫ g) ≫ sX) hY₂ (((V i).preimage g).ι ≫ g ≫ sX) ((hV.preimage g hY₁).isGoodPiece i)
      (g ≫ sX) hY₁ (g' := ((V i).preimage (h ≫ g)).ι) (f' := ((V i).preimage g).fromPreimage h)
      rfl rfl (Category.assoc h g sX).symm rfl 0
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage g hY₁) i).1
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage g hY₁) i).2
      (Subfunctor.isPullback_preimage h ((V i).preimage g)).flip hh k k (by simp) a)

/-- **Restriction to a piece commutes with flat pullback** (Stacks 0EPA): for `h : Y₂ ⟶ Y₁` flat
of relative dimension `m`, `(h^*α)|_{Y₂,i} = h_i^*(α|_{Y₁,i})`. -/
theorem chowGroupCanonicalPieceRestrict_flatPullback {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X)
    (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ)
    (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (i : I) (k n : ℤ)
    (hkn : k + (m : ℤ) = n) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    chowGroupCanonicalPieceRestrict (hV.preimage (h ≫ g) hY₂) i n
        (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf
          hhr k n hkn α) =
      flatPullbackChowMapCanonical.{u + 1} D
        (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
        (((V i).preimage g).ι ≫ g ≫ sX) ((hV.preimage g hY₁).isGoodPiece i)
        (((V i).preimage g).fromPreimage h) rfl m
        (isFlat_and_hasRelativeDimension_fromPreimage_preimage hV g hY₁ h hY₂ m hhf hhr i).1
        (isFlat_and_hasRelativeDimension_fromPreimage_preimage hV g hY₁ h hY₂ m hhf hhr i).2
        k n hkn (chowGroupCanonicalPieceRestrict (hV.preimage g hY₁) i k α) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  exact congrArg (chowClassCanonical.{u + 1} D (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX)
      ((hV.preimage (h ≫ g) hY₂).isGoodPiece i) n)
    (Subtype.ext (coe_flatPullbackMap_flatPullbackMap_of_comp_eq_comp D
      (((V i).preimage (h ≫ g)).ι ≫ (h ≫ g) ≫ sX) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
      ((h ≫ g) ≫ sX) hY₂ (((V i).preimage g).ι ≫ g ≫ sX) ((hV.preimage g hY₁).isGoodPiece i)
      (g ≫ sX) hY₁ ((V i).preimage (h ≫ g)).ι h (((V i).preimage g).fromPreimage h)
      ((V i).preimage g).ι rfl rfl (Category.assoc h g sX).symm rfl rfl 0 m m 0 (by omega)
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage (h ≫ g) hY₂) i).1
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage (h ≫ g) hY₂) i).2 hhf hhr
      (isFlat_and_hasRelativeDimension_fromPreimage_preimage hV g hY₁ h hY₂ m hhf hhr i).1
      (isFlat_and_hasRelativeDimension_fromPreimage_preimage hV g hY₁ h hY₂ m hhf hhr i).2
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage g hY₁) i).1
      (isFlat_and_hasRelativeDimension_zero_ι (hV.preimage g hY₁) i).2
      k n n k n hkn (by simp) (by simp) hkn a))

/-- Restriction to a piece commutes with the identification of Chow groups of equal degrees. -/
theorem chowGroupCanonicalPieceRestrict_chowGroupCanonicalDegreeCongr {Y : D.Ambient}
    {sY : Y ⟶ D.space} {R : I → Subfunctor Y}
    (hR : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (i : I) {a b : ℤ} (hab : a = b)
    (x : chowGroupCanonical.{u + 1} D sY hR.isGood a) :
    chowGroupCanonicalPieceRestrict hR i b (chowGroupCanonicalDegreeCongr D sY hR.isGood hab x) =
      chowGroupCanonicalDegreeCongr D ((R i).ι ≫ sY) (hR.isGoodPiece i) hab
        (chowGroupCanonicalPieceRestrict hR i a x) := by
  subst hab
  rfl

end Restriction

/-! ### Restriction to a piece and the Gysin maps -/

section Gysin

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L)

/-- **Stacks 0ER6 on Chow groups, in any target degree**: `(i')^*(f^*β) = g^*(i^*β)` with the
degree `k + r` of the target read as any `n` equal to it. -/
theorem sectionGysinChowGroupMap_flatPullbackChowMapCanonical_of_eq (k n : ℤ)
    (hn : k + (r : ℤ) = n) (hn₁ : k + 1 + (r : ℤ) = n + 1)
    (β : chowGroupCanonical.{u + 1} D p hp (k + 1)) :
    sectionGysinChowGroupMap D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)
        (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) n
        (flatPullbackChowMapCanonical.{u + 1} D p' hp' p hp f.hom hfbase r hflat hr (k + 1)
          (n + 1) hn₁ β) =
      flatPullbackChowMapCanonical.{u + 1} D
        ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) (pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
        (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase) r
        (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
          hfbase r hflat hr hL).1
        (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
          hfbase r hflat hr hL).2 k n hn
        (sectionGysinChowGroupMap D p hp L s hL k β) := by
  subst hn
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  exact sectionGysinChowGroupMap_flatPullbackChowMapCanonical D p hp p' hp' f hfbase r hflat hr L
    s hL k a

end Gysin

section GysinPiece

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
    {I : Type u} {V : I → Subfunctor X}
    (hV : IsClopenSubspaceDecomposition D sX fun i => (V i).ι) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (t : M.sections) (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (i : I)

/-- The inclusion of the piece `g^{-1}(X_i)` as a morphism of algebraic spaces. -/
abbrev pieceInclusion :
    (⟨((V i).preimage g).toFunctor, ((hV.preimage g hY).isGoodPiece i).1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩ :=
  ObjectProperty.homMk ((V i).preimage g).ι

/-- **The piece `Z(t)_i` of the vanishing locus is the vanishing locus `Z(t|_{Y_i})` of the
restricted section**: both are fibre products of `Z(t) ⟶ Y ⟵ Y_i`. -/
def pieceVanishingLocusIso :
    ((V i).preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)).toFunctor ≅
      (vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
        (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
        (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.toFunctor :=
  (Subfunctor.isPullback_preimage (vanishingLocus D (g ≫ sX) hY M t).1.ι
    ((V i).preimage g)).flip.isoIsPullback _ _
    (isPullback_pullbackVanishingLocusProjection D (g ≫ sX) hY
      ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
      (pieceInclusion hV g hY i) M t hM)

/-- The comparison isomorphism followed by the projection `Z(t|_{Y_i}) ⟶ Z(t)` is the inclusion
of the piece `Z(t)_i` into `Z(t)`. -/
theorem pieceVanishingLocusIso_hom_projection :
    (pieceVanishingLocusIso hV g hY M t hM i).hom ≫
        pullbackVanishingLocusProjection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t hM =
      ((V i).preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)).ι :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison isomorphism followed by the inclusion `Z(t|_{Y_i}) ⟶ Y_i` is the inclusion
of the piece `Z(t)_i` into `Y_i`. -/
theorem pieceVanishingLocusIso_hom_ι :
    (pieceVanishingLocusIso hV g hY M t hM i).hom ≫
        (vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.ι =
      ((V i).preimage g).fromPreimage (vanishingLocus D (g ≫ sX) hY M t).1.ι :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- As a test space over `X_i`, the piece `Z(t)_i` is `Z(t|_{Y_i})` along the comparison
isomorphism. -/
theorem pieceVanishingLocusIso_hom_comp_fromPreimage :
    (pieceVanishingLocusIso hV g hY M t hM i).hom ≫
        ((vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.ι ≫
        (V i).fromPreimage g) =
      (V i).fromPreimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) := by
  rw [← Category.assoc, pieceVanishingLocusIso_hom_ι]
  rfl

/-- The comparison isomorphism is a morphism over the base. -/
theorem pieceVanishingLocusIso_hom_comp_structure :
    (pieceVanishingLocusIso hV g hY M t hM i).hom ≫
        ((vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.ι ≫
        (V i).fromPreimage g ≫ (V i).ι ≫ sX) =
      (V i).fromPreimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫ (V i).ι ≫ sX := by
  rw [← Category.assoc, ← Category.assoc, pieceVanishingLocusIso_hom_ι]
  rfl

/-- The comparison isomorphism as a morphism of test spaces over `X_i`, as the base. -/
theorem pieceVanishingLocusIso_hom_comp_fromPreimage_comp :
    (pieceVanishingLocusIso hV g hY M t hM i).hom ≫
        (((vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.ι ≫
        (V i).fromPreimage g) ≫ (V i).ι ≫ sX) =
      (V i).fromPreimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫ (V i).ι ≫ sX := by
  rw [← Category.assoc, pieceVanishingLocusIso_hom_comp_fromPreimage]

/-- The comparison isomorphism is flat of relative dimension `0`. -/
theorem isFlat_and_hasRelativeDimension_pieceVanishingLocusIso :
    IsFlat D.site D.base D.base_mem (pieceVanishingLocusIso hV g hY M t hM i).hom ∧
      HasRelativeDimension 0 D.site D.base D.base_mem
        (pieceVanishingLocusIso hV g hY M t hM i).hom :=
  have hE := isEtale_of_isOpenImmersion D.site D.base D.base_mem
    (isOpenImmersion_of_isIso D.site D.base D.base_mem
      (pieceVanishingLocusIso hV g hY M t hM i).hom)
  ⟨isFlat_of_isEtale D.site D.base D.base_mem hE,
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem _
      (isGood_vanishingLocus _ _ _ _ _).1 hE⟩

/-- **Restriction to a piece commutes with the Gysin maps** (Stacks 0ER6): the restriction of
`i^*β` to the piece `Z(t)_i` is, along the comparison isomorphism `Z(t)_i ≅ Z(t|_{Y_i})`, the
Gysin map of the restricted section applied to `β|_{Y_i}`. -/
theorem chowGroupCanonicalPieceRestrict_sectionGysinChowGroupMap (k : ℤ)
    (β : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    chowGroupCanonicalPieceRestrict
        (hV.preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
          (isGood_vanishingLocus_comp D sX g hY M t)) i k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k β) =
      flatPullbackChowMapCanonical.{u + 1} D
        ((V i).fromPreimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) ≫ (V i).ι ≫ sX)
        ((hV.preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
          (isGood_vanishingLocus_comp D sX g hY M t)).isGoodPiece i)
        ((vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)).1.ι ≫
          (V i).fromPreimage g ≫ (V i).ι ≫ sX)
        (isGood_vanishingLocus D ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t))
        (pieceVanishingLocusIso hV g hY M t hM i).hom
        (pieceVanishingLocusIso_hom_comp_structure hV g hY M t hM i) 0
        (isFlat_and_hasRelativeDimension_pieceVanishingLocusIso hV g hY M t hM i).1
        (isFlat_and_hasRelativeDimension_pieceVanishingLocusIso hV g hY M t hM i).2 k k
        (by simp)
        (sectionGysinChowGroupMap D ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
          ((hV.preimage g hY).isGoodPiece i)
          (pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M)
          (pullbackGlobalSection D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M t)
          (isInvertibleSheaf_pullbackSheaf D (g ≫ sX) hY ((V i).fromPreimage g ≫ (V i).ι ≫ sX)
            ((hV.preimage g hY).isGoodPiece i) (pieceInclusion hV g hY i) M hM) k
          (chowGroupCanonicalPieceRestrict (hV.preimage g hY) i (k + 1) β)) := by
  have hι := isFlat_and_hasRelativeDimension_zero_ι (hV.preimage g hY) i
  have e := sectionGysinChowGroupMap_flatPullbackChowMapCanonical_of_eq D (g ≫ sX) hY
    ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
    (pieceInclusion hV g hY i) rfl 0 hι.1 hι.2 M t hM k k (by simp) (by simp) β
  have hφ := isFlat_and_hasRelativeDimension_pieceVanishingLocusIso hV g hY M t hM i
  refine Eq.trans ?_ (congrArg (flatPullbackChowMapCanonical.{u + 1} D _ _ _ _
    (pieceVanishingLocusIso hV g hY M t hM i).hom
    (pieceVanishingLocusIso_hom_comp_structure hV g hY M t hM i) 0 hφ.1 hφ.2 k k (by simp))
    e).symm
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective _ (sectionGysinChowGroupMap D (g ≫ sX) hY M t
    hM k β)
  rw [← hb]
  have hproj := isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D (g ≫ sX) hY
    ((V i).fromPreimage g ≫ (V i).ι ≫ sX) ((hV.preimage g hY).isGoodPiece i)
    (pieceInclusion hV g hY i) M t rfl 0 hι.1 hι.2 hM
  have hpι := isFlat_and_hasRelativeDimension_zero_ι
    (hV.preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
      (isGood_vanishingLocus_comp D sX g hY M t)) i
  exact congrArg (chowClassCanonical.{u + 1} D _ _ k) (Subtype.ext
    (coe_flatPullbackMap_flatPullbackMap_of_comp_eq D _ _ _ _ _ _
      (pieceVanishingLocusIso hV g hY M t hM i).hom _ _
      (pieceVanishingLocusIso_hom_projection hV g hY M t hM i) _ _ _ 0 0 0 rfl hφ.1 hφ.2
      hproj.1 hproj.2 hpι.1 hpι.2 k k k k (by simp) (by simp) (by simp) b).symm)

end GysinPiece

/-! ### The glued cap operations -/

section Glue

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
    {I : Type u} {V : I → Subfunctor X}
    (hV : IsClopenSubspaceDecomposition D sX fun i => (V i).ι) (p : ℤ)
    (c : ∀ (i : I) {Y : D.Ambient} (g : Y ⟶ (V i).toFunctor)
      (hY : D.IsGood (g ≫ (V i).ι ≫ sX)) (k : ℤ),
      chowGroupCanonical.{u + 1} D (g ≫ (V i).ι ≫ sX) hY k →+
        chowGroupCanonical.{u + 1} D (g ≫ (V i).ι ≫ sX) hY (k - p))

/-- **The cap operations glued along a decomposition into open and closed subspaces.** Given
maps `c_i ∩ - : CH_k(Y) ⟶ CH_{k-p}(Y)` on the good test spaces `Y ⟶ X_i` of the pieces, the map
`CH_k(X') ⟶ CH_{k-p}(X')` on a good test space `g : X' ⟶ X` which preserves the product
decompositions `CH_*(X') = ∏_i CH_*(X'_i)` and acts by `c_i ∩ -` on the factor of
`X'_i = g^{-1}(X_i)`. -/
def clopenGluedCap {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - p) :=
  (chowGroupCanonicalDecompositionEquiv (hV.preimage g hY) (k - p)).symm.toAddMonoidHom.comp
    ((AddMonoidHom.pi fun i =>
      (c i ((V i).fromPreimage g) ((hV.preimage g hY).isGoodPiece i) k).comp
        (Pi.evalAddMonoidHom _ i)).comp
      (chowGroupCanonicalDecompositionEquiv (hV.preimage g hY) k).toAddMonoidHom)

/-- **The glued cap operation acts by `c_i ∩ -` on the factor of `X'_i`.** -/
theorem chowGroupCanonicalPieceRestrict_clopenGluedCap {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) (i : I) :
    chowGroupCanonicalPieceRestrict (hV.preimage g hY) i (k - p) (clopenGluedCap hV p c g hY k α) =
      c i ((V i).fromPreimage g) ((hV.preimage g hY).isGoodPiece i) k
        (chowGroupCanonicalPieceRestrict (hV.preimage g hY) i k α) := by
  change chowGroupCanonicalDecompositionEquiv (hV.preimage g hY) (k - p)
    ((chowGroupCanonicalDecompositionEquiv (hV.preimage g hY) (k - p)).symm _) i = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- **The glued cap operation is characterized by its action on the factors**: a map with the
same restrictions to all the pieces is the glued one. -/
theorem eq_clopenGluedCap_of_chowGroupCanonicalPieceRestrict {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k)
    (β : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - p))
    (hβ : ∀ i, chowGroupCanonicalPieceRestrict (hV.preimage g hY) i (k - p) β =
      c i ((V i).fromPreimage g) ((hV.preimage g hY).isGoodPiece i) k
        (chowGroupCanonicalPieceRestrict (hV.preimage g hY) i k α)) :
    β = clopenGluedCap hV p c g hY k α :=
  chowGroupCanonical_ext_of_decomposition (hV.preimage g hY) fun i => by
    rw [hβ, chowGroupCanonicalPieceRestrict_clopenGluedCap]

/-- **The glued cap operation commutes with proper pushforward** when every `c_i ∩ -` does. -/
theorem clopenGluedCap_properPushforward
    (hproper : ∀ (i : I) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ (V i).toFunctor)
      (hY₁ : D.IsGood (g ≫ (V i).ι ≫ sX)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ (V i).ι ≫ sX)) (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ (V i).ι ≫ sX) hY₂ k),
      c i g hY₁ k (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁
          (Category.assoc h g _).symm hh k α) =
        chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g _).symm hh
          _ (c i (h ≫ g) hY₂ k α))
    {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁)
    (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    clopenGluedCap hV p c g hY₁ k (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁
        (Category.assoc h g sX).symm hh k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (clopenGluedCap hV p c (h ≫ g) hY₂ k α) := by
  refine (eq_clopenGluedCap_of_chowGroupCanonicalPieceRestrict hV p c g hY₁ k _ _ fun i => ?_).symm
  rw [chowGroupCanonicalPieceRestrict_properPushforward hV,
    chowGroupCanonicalPieceRestrict_properPushforward hV,
    chowGroupCanonicalPieceRestrict_clopenGluedCap]
  exact (hproper i ((V i).fromPreimage g) ((hV.preimage g hY₁).isGoodPiece i)
    (((V i).preimage g).fromPreimage h) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i)
    (isProper_fromPreimage_preimage hV g hY₁ h hY₂ hh i) k _).symm

/-- **The glued cap operation commutes with flat pullback** when every `c_i ∩ -` does. -/
theorem clopenGluedCap_flatPullback
    (hflat : ∀ (i : I) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ (V i).toFunctor)
      (hY₁ : D.IsGood (g ≫ (V i).ι ≫ sX)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ (V i).ι ≫ sX)) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
      (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ (V i).ι ≫ sX) hY₁ k),
      c i (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g _).symm m hhf hhr k (k + m) rfl α) =
        flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g _).symm m hhf
          hhr (k - p) (k + m - p) (by ring) (c i g hY₁ k α))
    {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁)
    (hY₂ : D.IsGood ((h ≫ g) ≫ sX)) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    clopenGluedCap hV p c (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
        (Category.assoc h g sX).symm m hhf hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - p) (k + m - p) (by ring) (clopenGluedCap hV p c g hY₁ k α) := by
  refine (eq_clopenGluedCap_of_chowGroupCanonicalPieceRestrict hV p c (h ≫ g) hY₂ (k + m) _ _
    fun i => ?_).symm
  have H := isFlat_and_hasRelativeDimension_fromPreimage_preimage hV g hY₁ h hY₂ m hhf hhr i
  rw [chowGroupCanonicalPieceRestrict_flatPullback hV,
    chowGroupCanonicalPieceRestrict_flatPullback hV,
    chowGroupCanonicalPieceRestrict_clopenGluedCap]
  exact (hflat i ((V i).fromPreimage g) ((hV.preimage g hY₁).isGoodPiece i)
    (((V i).preimage g).fromPreimage h) ((hV.preimage (h ≫ g) hY₂).isGoodPiece i) m H.1 H.2 k
    _).symm

/-- **The glued cap operation commutes with the Gysin maps** of the sections of invertible
modules when every `c_i ∩ -` commutes with them and with flat pullback. -/
theorem clopenGluedCap_sectionGysinChowGroupMap
    (hflat : ∀ (i : I) {Y₁ Y₂ : D.Ambient} (g : Y₁ ⟶ (V i).toFunctor)
      (hY₁ : D.IsGood (g ≫ (V i).ι ≫ sX)) (h : Y₂ ⟶ Y₁)
      (hY₂ : D.IsGood ((h ≫ g) ≫ (V i).ι ≫ sX)) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
      (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ (V i).ι ≫ sX) hY₁ k),
      c i (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g _).symm m hhf hhr k (k + m) rfl α) =
        flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g _).symm m hhf
          hhr (k - p) (k + m - p) (by ring) (c i g hY₁ k α))
    (hgysin : ∀ (i : I) {Y : D.Ambient} (g : Y ⟶ (V i).toFunctor)
      (hY : D.IsGood (g ≫ (V i).ι ≫ sX)) (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
      (t : M.sections) (hM : IsInvertibleSheaf D (g ≫ (V i).ι ≫ sX) hY M) (k : ℤ)
      (α : chowGroupCanonical.{u + 1} D (g ≫ (V i).ι ≫ sX) hY (k + 1)),
      c i ((vanishingLocus D (g ≫ (V i).ι ≫ sX) hY M t).1.ι ≫ g)
          (isGood_vanishingLocus_comp D ((V i).ι ≫ sX) g hY M t) k
          (sectionGysinChowGroupMap D (g ≫ (V i).ι ≫ sX) hY M t hM k α) =
        sectionGysinChowGroupMap D (g ≫ (V i).ι ≫ sX) hY M t hM (k - p)
          (chowGroupCanonicalDegreeCongr D (g ≫ (V i).ι ≫ sX) hY (by ring) (c i g hY (k + 1) α)))
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    clopenGluedCap hV p c ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
        (isGood_vanishingLocus_comp D sX g hY M t) k
        (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - p)
        (chowGroupCanonicalDegreeCongr D (g ≫ sX) hY (by ring)
          (clopenGluedCap hV p c g hY (k + 1) α)) := by
  refine (eq_clopenGluedCap_of_chowGroupCanonicalPieceRestrict hV p c _
    (isGood_vanishingLocus_comp D sX g hY M t) k _ _ fun i => ?_).symm
  rw [chowGroupCanonicalPieceRestrict_sectionGysinChowGroupMap hV,
    chowGroupCanonicalPieceRestrict_sectionGysinChowGroupMap hV,
    chowGroupCanonicalPieceRestrict_chowGroupCanonicalDegreeCongr,
    chowGroupCanonicalPieceRestrict_clopenGluedCap]
  have hφ := isFlat_and_hasRelativeDimension_pieceVanishingLocusIso hV g hY M t hM i
  have e1 := cap_flatPullbackChowMapCanonical_of_comp_eq D ((V i).ι ≫ sX) p (c i) (hflat i)
    _ (isGood_vanishingLocus_comp D ((V i).ι ≫ sX) ((V i).fromPreimage g)
      ((hV.preimage g hY).isGoodPiece i) _ _)
    ((V i).fromPreimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g))
    ((hV.preimage ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g)
      (isGood_vanishingLocus_comp D sX g hY M t)).isGoodPiece i)
    (pieceVanishingLocusIso hV g hY M t hM i).hom
    (pieceVanishingLocusIso_hom_comp_fromPreimage hV g hY M t hM i)
    (pieceVanishingLocusIso_hom_comp_fromPreimage_comp hV g hY M t hM i) 0 hφ.1 hφ.2 k k
    (by simp) (by simp)
  exact ((e1 _).trans (congrArg (DFunLike.coe (flatPullbackChowMapCanonical.{u + 1} D _ _ _ _
    (pieceVanishingLocusIso hV g hY M t hM i).hom
    (pieceVanishingLocusIso_hom_comp_structure hV g hY M t hM i) 0 hφ.1 hφ.2 (k - p) (k - p)
    (by simp))) (hgysin i _ _ _ _ _ _ _))).symm

end Glue

end AlgebraicGeometry.Space
