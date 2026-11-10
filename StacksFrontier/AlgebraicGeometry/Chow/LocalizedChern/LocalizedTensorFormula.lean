module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedTensor
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedRankChoose
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedMulLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedProductBilinear
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedTransportComposite
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyDirectSum

/-!
# The localized classes of a derived tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z₁, Z₂ ⊆ X` be closed subschemes and let `F₁, F₂ ∈ D(𝒪_X)` be perfect
with `F_i|_{X ∖ Z_i}` zero. Lemma 0FBF expresses the localized classes of `F₁ ⊗^L F₂` along
`Z₁ ∩ Z₂` through those of `F₁` and `F₂`; for the power sum classes

  `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, F₁) P_{p₂}(Z₂ ⟶ X, F₂)`

in `A^p(Z₁ ∩ Z₂ ⟶ X)`, the products being those of Stacks 0FE5
(`Stacks.Chow.supportedIntersectionMul`).

The proof is the source's. When `F₁`, `F₂` and `F₁ ⊗^L F₂` are represented by locally bounded
complexes of finite locally free modules, choose the graph constructions `b_i : W_i ⟶ 𝐏¹_X`,
`Q_i`, `T_i` for `F_i` and the common modification `W = W₁ ×_{𝐏¹_X} W₂`, pull `Q_i` and `T_i`
back to `W`, and take `Q₁ ⊗^L Q₂` with `T₁ ∪ T₂` for `F₁ ⊗^L F₂`. By Stacks 0FE8 the three
localized classes are the classes of Stacks 0F9K of these data on `W`, and on `W` the formula is
`Stacks.Chow.modificationPowerSum_derivedTensor` (Stacks 0FE5 and 0FE7). In general the classes are
those of Remark 0GUK, and the identity descends from an envelope on which the three objects are
such complexes (`Stacks.Chow.localizedPowerSum_derivedTensor_of_isEnvelope`).

## Main results

* `Stacks.Chow.localizedPowerSum_derivedTensor_of_isLocallyBoundedFiniteLocallyFree` — the formula
  for `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` when the three objects are represented by locally bounded
  complexes of finite locally free modules, `Z₁ ∩ Z₂` presented by any pullback square.
* `Stacks.Chow.LocalizedChernData.localizedPowerSum_derivedTensorOfIsZero` — the formula for the
  classes of Remark 0GUK, for `F₁`, `F₂` whose Chern classes are defined.
* `Stacks.Chow.bivariantTransport_supportedIntersectionMul` — the product of Stacks 0FE5 does not
  depend on the pullback square presenting `Z₁ ∩ Z₂`, up to transport along the comparison.

## Implementation notes

The class of Stacks 0F9K of `Q₁ ⊗^L Q₂` is computed on `Z₁ ×_X Z₂` mapping to `X` through `Z₁`
(`Stacks.Chow.modificationPowerSum_derivedTensor`), while `Z₁ ∩ Z₂` is an arbitrary pullback
square in the statements. The two are compared through the identification `Z₁ ∩ Z₂ ≅ Z₁ ×_X Z₂`
over `X`: by Stacks 0FB7 the localized class for `Z₁ ×_X Z₂` is the pushforward along it of the one
for `Z₁ ∩ Z₂`, that is its transport (`Stacks.Chow.bivariantTransport`), and transport is
injective.

On `W` every object is again represented by a locally bounded complex of finite locally free
modules (Stacks 0F90 (5) for `Q_i`, pullback and total tensor complex), so alternative (c) of
condition (3) of Situation 0GUJ holds there, as Stacks 0FE8 requires.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section TransportDegree

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)

/-- Transport along an isomorphism commutes with reading a class in an equal degree. -/
theorem bivariantTransport_bivariantClassDegreeCongr (hgys : G.IsNaturalUnderBaseChangeIso)
    {p p' : ℤ} (e : p = p') (c : BivariantClass C G sA sW v hv p) :
    bivariantTransport C G sA sB sW v hv u hu θ hθ p' hgys
        (bivariantClassDegreeCongr C G sA sW v hv e c) =
      bivariantClassDegreeCongr C G sB sW u hu e
        (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c) := by
  subst e
  rfl

end TransportDegree

section Presentation

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W W' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  {w₁' : W' ⟶ Z₁} {w₂' : W' ⟶ Z₂} (sq' : IsPullback w₁' w₂' f₁ f₂)
  (iW : W ⟶ X) [LocallyOfFiniteType iW] (hW : w₂ ≫ f₂ = iW)
  (iW' : W' ⟶ X) [LocallyOfFiniteType iW'] [Mono iW'] (hW' : w₂' ≫ f₂ = iW') {p q : ℤ}

/-- **The product of Stacks 0FE5 does not depend on the square presenting `Z₁ ∩ Z₂`.** For two
pullback squares presenting `W` and `W'` as `Z₁ ×_X Z₂`, with `W' ⟶ X` a monomorphism, the
transport along any isomorphism `θ : W ≅ W'` over `X` of the product for `W` is the product for
`W'`. -/
theorem bivariantTransport_supportedIntersectionMul (θ : W ≅ W') (hθ : θ.hom ≫ iW' = iW)
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    bivariantTransport C (gysinSystemOfInvertible C) (iW ≫ sX) (iW' ≫ sX) sX iW rfl iW' rfl θ hθ
        (p + q) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂) =
      supportedIntersectionMul C sX f₁ f₂ sq' iW' hW' c₁ c₂ := by
  unfold supportedIntersectionMul
  rw [bivariantTransport_bivariantTransport]
  have hiso : sq.isoPullback.symm ≪≫ θ = sq'.isoPullback.symm := by
    refine Iso.ext ?_
    rw [← cancel_mono iW', Iso.trans_hom, Category.assoc, hθ,
      isoPullback_inv_comp_eq f₁ f₂ sq iW hW, isoPullback_inv_comp_eq f₁ f₂ sq' iW' hW']
  congr 1

end Presentation

section Complexes

variable {X : Scheme.{u}}

/-- The derived tensor product of two objects represented by locally bounded complexes of finite
locally free modules is represented by one, their total tensor complex. -/
theorem exists_isLocallyBoundedFiniteLocallyFree_derivedTensor {E₁ E₂ : DerivedCategory X.Modules}
    (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁))
    (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₂)) :
    ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅
          ((derivedTensorProductFunctor X.sheaf).obj E₁).obj E₂) := by
  obtain ⟨P₁, hP₁, ⟨e₁⟩⟩ := hc₁
  obtain ⟨P₂, hP₂, ⟨e₂⟩⟩ := hc₂
  exact ⟨tensorTotal P₁ P₂, isLocallyBoundedFiniteLocallyFree_tensorTotal hP₁ hP₂,
    ⟨(derivedTensorQIso P₁ P₂ hP₂).symm ≪≫ derivedTensorMapIso e₁ e₂⟩⟩

end Complexes

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {W : Scheme.{u}} (b : W ⟶ projectiveLineProduct S.a)
  [IsProper b] (hA : IsIso (pullback.snd b (projectiveLineAffineChart S.a)))
  (g : W ⟶ graphBlowup S.a S.E S.perfect) (hb : g ≫ graphBlowupToBase S.a S.E S.perfect = b)
  (hfin : LocalizedChernFiniteness S.base (modificationProjection S.a b ≫ S.a)
    ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect)))

/-- The closed subscheme `T' ⊆ W_∞` of the graph construction on which `Q` is zero: the open and
closed part (`Stacks.Chow.graphZeroLocus`) of the closed subscheme `T` of Stacks 0F90 (3), (4) on
which every cohomology sheaf of `Q|_T` has rank `0`. It is the closed subscheme of the definition
of `P_p(Z ⟶ X, E)` (`Stacks.Chow.LocalizedSituation.localizedPowerSum`). -/
abbrev graphZeroSubschemeι :
    (graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology).toScheme ⟶
      modificationFibreAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect) :=
  (graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology).ι ≫ S.graphSubschemeι

/-- `T' ⊆ W_∞` is a closed subscheme. -/
instance isClosedImmersion_graphZeroSubschemeι : IsClosedImmersion S.graphZeroSubschemeι := by
  have := isClosedImmersion_graphZeroLocus_ι S.a S.E S.perfect S.graphSubschemeι
    S.isFiniteLocallyFree_graphObjectRestrictHomology
  exact IsClosedImmersion.comp _ _

/-- The inverse image in `W'_∞` of the closed subscheme `T'` of the graph construction is a closed
subscheme. -/
instance isClosedImmersion_pullbackSnd_graphZeroSubschemeι :
    IsClosedImmersion (pullback.snd (S.graphZeroSubschemeι ≫
      modificationInclusionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
      (modificationInclusionAtInfinity S.a b ≫ g)) := inferInstance

/-- **The restriction of `Q` to `b^{-1}(𝐀¹_X)` is the pullback of `E`**, for the graph
construction `b : W ⟶ 𝐏¹_X`, `Q` of `E` (Stacks 0F90 (2)). -/
theorem nonempty_derivedPullback_affineChart_graphObject :
    Nonempty ((derivedPullback (pullback.fst (graphBlowupToBase S.a S.E S.perfect)
        (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect) ≅
      (derivedPullback (pullback.fst (graphBlowupToBase S.a S.E S.perfect)
        (projectiveLineAffineChart S.a) ≫
          modificationProjection S.a (graphBlowupToBase S.a S.E S.perfect)).toLRSHom.toShHom).obj
        S.E) :=
  nonempty_derivedPullback_graphObject S.a S.E S.perfect
    (pullback.fst (graphBlowupToBase S.a S.E S.perfect) (projectiveLineAffineChart S.a))
    fun v ↦ ⟨pullback.snd (graphBlowupToBase S.a S.E S.perfect) (projectiveLineAffineChart S.a) v,
      by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩

omit [IsProper b] in
include hb in
/-- The inverse image in `W'_∞` of the closed subscheme `T'` of the graph construction contains
every point of `W'_∞` over `X ∖ Z`, for a morphism `g : W' ⟶ W` of modifications. -/
theorem mem_range_pullbackSnd_graphZeroSubschemeι (h : S.IsZeroOnComplement) :
    ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i →
      w ∈ Set.range (pullback.snd (S.graphZeroSubschemeι ≫
        modificationInclusionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
        (modificationInclusionAtInfinity S.a b ≫ g)) :=
  mem_range_pullbackSnd_of_notMem_range S.a g hb S.i _
    (mem_range_graphZeroLocus S.base S.a S.E S.perfect S.i S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology S.mem_range_graphSubschemeι
      (S.finiteLocallyFreeRank_graphSubscheme_eq_zero h))

omit [IsProper b] in
/-- The pullback `Lg^*Q` of the object of the graph construction restricts to zero on the inverse
image in `W'_∞` of the closed subscheme `T'`. -/
theorem isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι :
    IsZero ((derivedPullback (pullback.snd (S.graphZeroSubschemeι ≫
        modificationInclusionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
        (modificationInclusionAtInfinity S.a b ≫ g) ≫
          modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
      ((derivedPullback g.toLRSHom.toShHom).obj (graphObject S.a S.E S.perfect))) :=
  isZero_derivedPullback_derivedPullback_pullbackSnd S.a g _
    (isZero_derivedPullback_graphZeroLocus S.a S.E S.perfect S.graphSubschemeι
      S.isFiniteLocallyFree_graphObjectRestrictHomology)

include hb hfin in
/-- **The class `P_p(Z ⟶ X, E)` of Stacks 0FB2 on a modification dominating the graph
construction** (Stacks 0FE8). Let `b : W' ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and
let `g : W' ⟶ W` be a morphism to the modification of the graph construction of `E` over `𝐏¹_X`.
If `Lg^*Q` satisfies condition (3) of Situation 0GUJ on `W'`, then `P_p(Z ⟶ X, E)` is the class
of Stacks 0F9K of `Lg^*Q` and the inverse image in `W'_∞` of the closed subscheme `T'`. -/
theorem modificationPowerSum_derivedPullback_graphObject (h : S.IsZeroOnComplement) (p : ℕ) :
    modificationPowerSum S.base S.a b hA S.i
        (pullback.snd (S.graphZeroSubschemeι ≫
          modificationInclusionAtInfinity S.a (graphBlowupToBase S.a S.E S.perfect))
          (modificationInclusionAtInfinity S.a b ≫ g))
        (S.hasDefinedChernClasses_graphObject.derivedPullback g) p
        (S.mem_range_pullbackSnd_graphZeroSubschemeι b g hb h)
        (S.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b g) =
      S.localizedPowerSum h p :=
  S.modificationPowerSum_eq_localizedPowerSum b hA _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
      (isPerfect_graphObject S.base S.a S.E S.perfect)) hfin
    (nonempty_derivedPullback_affineChart_derivedPullback_iso S.a g hb
      S.nonempty_derivedPullback_affineChart_graphObject) p _ _ h

end LocalizedSituation

section TensorFormula

variable (C : ChowSituation.{u}) {X Z₁ Z₂ Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (z₁ : Z₁ ⟶ X) [IsClosedImmersion z₁] (z₂ : Z₂ ⟶ X) [IsClosedImmersion z₂]
  {w₁ : Z ⟶ Z₁} {w₂ : Z ⟶ Z₂} (sq : IsPullback w₁ w₂ z₁ z₂) (z : Z ⟶ X) [IsClosedImmersion z]
  (hz : w₂ ≫ z₂ = z) {E₁ E₂ E : DerivedCategory X.Modules}
  (hE₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
  (hE₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₂)
  (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
  (h₁ : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z₁.base)ᶜ,
    z₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E₁))
  (h₂ : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z₂.base)ᶜ,
    z₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E₂))
  (h : IsZero ((derivedPullback (X.toRingedSpace.ofRestrict (⟨(Set.range z.base)ᶜ,
    z.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E))
  (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₁))
  (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E₂))
  (hc : ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
    IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E))
  (e : E ≅ ((derivedTensorProductFunctor X.sheaf).obj E₁).obj E₂)

include e in
/-- **The formula of Lemma 0FBF for `P_p` when the objects are complexes.** Let `Z₁, Z₂ ⊆ X` be
closed, `Z₁ ∩ Z₂` presented by a pullback square, and let `E₁, E₂, E ∈ D(𝒪_X)` be perfect, each
represented by a locally bounded complex of finite locally free modules, with `E_i|_{X ∖ Z_i}` and
`E|_{X ∖ Z₁ ∩ Z₂}` zero and `E ≅ E₁ ⊗^L E₂`. Then for the classes of Stacks 0FB2

  `P_p(Z₁ ∩ Z₂ ⟶ X, E) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, E₁) P_{p₂}(Z₂ ⟶ X, E₂)`

in `A^p(Z₁ ∩ Z₂ ⟶ X)`. -/
theorem localizedPowerSum_derivedTensor_of_isLocallyBoundedFiniteLocallyFree (p : ℕ) :
    ((LocalizedChernData.ofIsZero C f z E hE h 0).toSituation hc).localizedPowerSum h p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C f z₁ z₂ sq z hz
            (((LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁).localizedPowerSum
              h₁ q.1.1)
            (((LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂).localizedPowerSum
              h₂ q.1.2)) := by
  let S₁ := (LocalizedChernData.ofIsZero C f z₁ E₁ hE₁ h₁ 0).toSituation hc₁
  let S₂ := (LocalizedChernData.ofIsZero C f z₂ E₂ hE₂ h₂ 0).toSituation hc₂
  let S := (LocalizedChernData.ofIsZero C f z E hE h 0).toSituation hc
  let b₁ := graphBlowupToBase f E₁ hE₁
  let b₂ := graphBlowupToBase f E₂ hE₂
  have hA : IsIso (pullback.snd (pullback.fst b₁ b₂ ≫ b₁) (projectiveLineAffineChart f)) :=
    isIso_pullbackSnd_pullbackFst_comp_projectiveLineAffineChart f b₁ b₂
      (isIso_pullback_snd_graphBlowupToBase f E₁ hE₁)
      (isIso_pullback_snd_graphBlowupToBase f E₂ hE₂)
  let b := pullback.fst b₁ b₂ ≫ b₁
  have : IsProper b₁ := isProper_graphBlowupToBase f E₁ hE₁
  have : IsProper b₂ := isProper_graphBlowupToBase f E₂ hE₂
  have : IsProper b := by dsimp only [b]; infer_instance
  have hb₂ : pullback.snd b₁ b₂ ≫ b₂ = b := pullback.condition.symm
  have hp₁ := exists_isLocallyBoundedFiniteLocallyFree_derivedPullback
    (pullback.fst b₁ b₂)
    (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₁ hE₁ hc₁)
  have hp₂ := exists_isLocallyBoundedFiniteLocallyFree_derivedPullback
    (pullback.snd b₁ b₂)
    (exists_isLocallyBoundedFiniteLocallyFree_graphObject f E₂ hE₂ hc₂)
  have key₁ := S₁.modificationPowerSum_derivedPullback_graphObject b hA (pullback.fst b₁ b₂) rfl
    (Or.inr (Or.inr (Or.inl hp₁))) h₁
  have key₂ := S₂.modificationPowerSum_derivedPullback_graphObject b hA (pullback.snd b₁ b₂) hb₂
    (Or.inr (Or.inr (Or.inl hp₂))) h₂
  let t₁ : _ ⟶ modificationFibreAtInfinity f b :=
    pullback.snd (S₁.graphZeroSubschemeι ≫ modificationInclusionAtInfinity f b₁)
      (modificationInclusionAtInfinity f b ≫ pullback.fst b₁ b₂)
  let t₂ : _ ⟶ modificationFibreAtInfinity f b :=
    pullback.snd (S₂.graphZeroSubschemeι ≫ modificationInclusionAtInfinity f b₂)
      (modificationInclusionAtInfinity f b ≫ pullback.snd b₁ b₂)
  have : IsClosedImmersion t₁ :=
    S₁.isClosedImmersion_pullbackSnd_graphZeroSubschemeι b (pullback.fst b₁ b₂)
  have : IsClosedImmersion t₂ :=
    S₂.isClosedImmersion_pullbackSnd_graphZeroSubschemeι b (pullback.snd b₁ b₂)
  have hm₁ := S₁.mem_range_pullbackSnd_graphZeroSubschemeι b (pullback.fst b₁ b₂) rfl h₁
  have hm₂ := S₂.mem_range_pullbackSnd_graphZeroSubschemeι b (pullback.snd b₁ b₂) hb₂ h₂
  have hz₁ := S₁.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b (pullback.fst b₁ b₂)
  have hz₂ := S₂.isZero_derivedPullback_pullbackSnd_graphZeroSubschemeι b (pullback.snd b₁ b₂)
  have hQp₁ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.fst b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₁ hE₁)
  have hQp₂ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (pullback.snd b₁ b₂).toLRSHom.toShHom _ (isPerfect_graphObject C f E₂ hE₂)
  have hF₂ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.snd b₁ b₂) hb₂
    S₂.nonempty_derivedPullback_affineChart_graphObject
  have hres₂ := S₂.modificationRestriction_of_isZero b t₂ (modificationComplementOpens b z₂)
    (fun _ hw => S₂.modificationProjection_notMem_range hw) hQp₂ h₂ hF₂
    hm₂ hz₂
  have L1 := modificationPowerSum_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂
    (S₁.hasDefinedChernClasses_graphObject.derivedPullback _)
    (S₂.hasDefinedChernClasses_graphObject.derivedPullback _)
    hm₁ hm₂ hz₁ hz₂ hA hres₂ (Or.inr (Or.inr (Or.inl hp₂))) p
  -- the tensor product on the common modification
  have hF₁ := nonempty_derivedPullback_affineChart_derivedPullback_iso f (pullback.fst b₁ b₂) rfl
    S₁.nonempty_derivedPullback_affineChart_graphObject
  have hθ : sq.isoPullback.hom ≫ pullback.fst z₁ z₂ ≫ z₁ = z := by
    rw [IsPullback.isoPullback_hom_fst_assoc, sq.w, hz]
  let S' := S.withLargerClosed (pullback.fst z₁ z₂ ≫ z₁) sq.isoPullback.hom hθ
  have h' : S'.IsZeroOnComplement :=
    LocalizedSituation.IsZeroOnComplement.withLargerClosed (S := S) h
  have hfin : LocalizedChernFiniteness C (modificationProjection f b ≫ f)
      (((derivedTensorProductFunctor (pullback b₁ b₂).sheaf).obj
        ((derivedPullback (pullback.fst b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₁ hE₁))).obj
        ((derivedPullback (pullback.snd b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₂ hE₂))) :=
    Or.inr (Or.inr (Or.inl (exists_isLocallyBoundedFiniteLocallyFree_derivedTensor hp₁ hp₂)))
  have hF : Nonempty _ := (nonempty_derivedPullback_derivedTensor_iso _ _ hF₁ hF₂).map
    (· ≪≫ (derivedPullback _).mapIso e.symm)
  have : IsProper (show _ ⟶ projectiveLineProduct S'.a from b) := ‹IsProper b›
  have : IsClosedImmersion (show _ ⟶ modificationFibreAtInfinity S'.a b from
    (reducedUnionIdeal t₁ t₂).subschemeι) :=
    inferInstanceAs (IsClosedImmersion (reducedUnionIdeal t₁ t₂).subschemeι)
  have key := S'.modificationPowerSum_eq_localizedPowerSum b hA
    (reducedUnionIdeal t₁ t₂).subschemeι
    (RingedSpace.isPerfect_canonicalDerivedTensorProduct (pullback b₁ b₂).toRingedSpace
      ((derivedPullback (pullback.fst b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₁ hE₁))
      ((derivedPullback (pullback.snd b₁ b₂).toLRSHom.toShHom).obj (graphObject f E₂ hE₂))
      hQp₁ hQp₂) hfin hF p
    (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hm₁ hm₂)
    (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hz₁ hz₂) h'
  have hgys : (gysinSystemOfInvertible C).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C
  have h7 := LocalizedSituation.localizedPowerSum_withLargerClosed (S := S)
    (i' := pullback.fst z₁ z₂ ≫ z₁) (j := sq.isoPullback.hom) (hj := hθ)
    h p
  have htr : bivariantTransport C (gysinSystemOfInvertible C) (z ≫ f)
      ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback hθ p
      hgys (S.localizedPowerSum h p) = S'.localizedPowerSum h' p :=
    (bivariantTransport_eq_bivariantProperPushforward_of_eq sq.isoPullback hθ rfl rfl
      (by rw [← Category.assoc, hθ]) _
      ((S.localizedPowerSum h p).congrHom hθ.symm (by rw [hθ]))
      (BivariantClass.congrHom_heq _ _ _)).trans h7.symm
  refine bivariantTransport_injective C (gysinSystemOfInvertible C) (z ≫ f)
    ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback hθ p
    hgys ?_
  refine htr.trans (key.symm.trans (L1.trans ?_))
  have hT : ∀ c, bivariantTransport C (gysinSystemOfInvertible C) (z ≫ f)
      ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback hθ p
      hgys c = bivariantTransportAddHom C (gysinSystemOfInvertible C) (z ≫ f)
      ((pullback.fst z₁ z₂ ≫ z₁) ≫ f) f z rfl (pullback.fst z₁ z₂ ≫ z₁) rfl sq.isoPullback hθ p
      hgys c := fun _ ↦ rfl
  rw [hT, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, ← hT, bivariantTransport_bivariantClassDegreeCongr,
    bivariantTransport_supportedIntersectionMul C f z₁ z₂ sq (IsPullback.of_hasPullback z₁ z₂) z hz
      _ pullback.condition.symm, key₁, key₂]

end TensorFormula

section Downstairs

variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₂]
  {F₁ F₂ : DerivedCategory X.Modules}
  (hF₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₁)
  (hF₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₂)
  (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₁.base)ᶜ,
        i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₁))
  (h₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₂.base)ᶜ,
        i₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₂))
  (hE₁ : HasDefinedChernClasses F₁) (hE₂ : HasDefinedChernClasses F₂)
  (hE : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂))

/-- **The formula of Lemma 0FBF for `P_p`, for the classes of Remark 0GUK.** Let `Z₁, Z₂ ⊆ X` be
closed and `F₁, F₂ ∈ D(𝒪_X)` perfect with `F_i|_{X ∖ Z_i}` zero and with defined Chern classes.
Then

  `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, F₁) P_{p₂}(Z₂ ⟶ X, F₂)`

in `A^p(Z₁ ∩ Z₂ ⟶ X)`, for `Z₁ ∩ Z₂ = Z₁ ×_X Z₂`. On the envelope of the tensor product of the
presentations of `F₁` and `F₂` the three objects are complexes, and the formula there
(`Stacks.Chow.localizedPowerSum_derivedTensor_of_isLocallyBoundedFiniteLocallyFree`) descends
(`Stacks.Chow.localizedPowerSum_derivedTensor_of_isEnvelope`). -/
theorem LocalizedChernData.localizedPowerSum_derivedTensorOfIsZero (p : ℕ) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0).localizedPowerSum hE
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ q.1.1)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ q.1.2)) := by
  let H := hE₁.some.tensor hE₂.some
  have hc₁ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorLeft hE₂.some)
  have hc₂ := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (hE₁.some.tensorRight hE₂.some)
  have hc := EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree H
  have hY := localizedPowerSum_derivedTensor_of_isLocallyBoundedFiniteLocallyFree C (H.f ≫ a)
      (pullback.snd i₁ H.f) (pullback.snd i₂ H.f)
      (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
        (pullback.snd i₁ i₂ ≫ i₂) rfl H.f)
      (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) H.f) (by simp)
      (LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0 |>.pullback H.f).perfect
      (LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0 |>.pullback H.f).perfect
      (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0 |>.pullback H.f).perfect
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) (f := H.f) h₁)
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) (f := H.f) h₂)
      (LocalizedChernData.IsZeroOnComplement.pullback
        (D := LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0) (f := H.f)
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂)) hc₁ hc₂ hc
      (derivedPullbackDerivedTensorIso H.f F₁ F₂) p
  exact localizedPowerSum_derivedTensor_of_isEnvelope C a i₁ i₂ hF₁ hF₂ h₁ h₂ H.f hE₁ hE₂ hE
    H.envelope hc₁ hc₂ hc p hY

end Downstairs

end Stacks.Chow

end
