module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityClass
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCase
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Modification

/-!
# Preparation for localized Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, and let `b : W ⟶ 𝐏¹_X` be a proper
morphism which is an isomorphism over `𝐀¹_X`, with fibre at infinity `W_∞ ⊆ W` and section at
zero `i_0 : X ⟶ W`. Let `Q ∈ D(𝒪_W)` have defined Chern classes, and let `T ⊆ W_∞` be a closed
subscheme containing every point of `W_∞` lying over `X ∖ Z` such that `Q|_T` is zero, resp.
isomorphic to a finite locally free module of rank `< p` in degree `0`. Stacks 0F9K constructs a
class

  `P'_p(Q) = (E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`,
  resp. `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`,

where `E = W_∞ ×_X Z`, `P'_p(Q|_E)`, resp. `c'_p(Q|_E)`, in `A^p(E ⟶ W_∞)` is the class of
Stacks 0F9H for the closed cover `W_∞ = T ∪ E`, and `C ∈ A⁰(W_∞ ⟶ X)` is the class of
Stacks 0F9J, and proves

  `(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})`,   resp.   `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})`.

This is the instance of the construction `Stacks.Chow.localizedModificationClass` at the class
`q = P_p(Q) ∈ A^p(W)`, resp. `q = c_p(Q)`, which vanishes over `T` because `Q|_T` is zero, resp.
has rank `< p`, and at the class of Stacks 0F9J; the identity is the instance of
`Stacks.Chow.properPushforwardChowCohomology_localizedModificationClass`, whose right side
`i_0^* q` is `P_p(Li_0^* Q)`, resp. `c_p(Li_0^* Q)`, by the compatibility of these classes with
restriction.

## Main definitions

* `Stacks.Chow.modificationPowerSum` — the class `P'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K.
* `Stacks.Chow.modificationChernClass` — the class `c'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K.

## Main results

* `Stacks.Chow.TotalChowClass.res_apply_eq_bivariantClassCongrBase` — a component of the
  restriction of a total class, for an arbitrary structure morphism of the source, is the
  restriction of the component.
* `Stacks.Chow.properPushforwardChowCohomology_modificationPowerSum`,
  `Stacks.Chow.properPushforwardChowCohomology_modificationChernClass` — Stacks 0F9K:
  `(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})` and `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})`.

## Implementation notes

The source assumes `Q` perfect. The constructions and the identities only use that the Chern
classes of `Q` are defined (`Stacks.Chow.HasDefinedChernClasses`); perfectness is therefore not
assumed. The Chern classes of `Q|_{X × {0}}` are then defined by
`Stacks.Chow.HasDefinedChernClasses.derivedPullback`.

The divisor `W_∞` is `Stacks.Chow.modificationFibreAtInfinity`, the hypothesis that `b` is an
isomorphism over `𝐀¹_X` is that the base change of `b` along
`Stacks.Chow.projectiveLineAffineChart` is an isomorphism, and `Q|_{X × {0}}` is the derived
pullback of `Q` along the section at zero `Stacks.Chow.modificationSectionAtZero`. The hypothesis
on `T` is stated pointwise, as in the source; the restriction `Q|_T` is the derived pullback along
`T ⟶ W_∞ ⟶ W`.

## References

* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Components of a restricted total class -/

/-- The component of degree `p` of the restriction of a total class along `h : Y' ⟶ Y`, the
structure morphism of `Y'` being presented by an equality `h ≫ sY = sY'`, is the restriction of
Stacks 0B7F of the component of degree `p`, read against `sY'`. -/
theorem TotalChowClass.res_apply_eq_bivariantClassCongrBase {C : ChowSituation.{u}}
    {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) (p : ℕ) :
    TotalChowClass.res h hs c p =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y') hs hs
        (hv := Category.id_comp _) (hv' := Category.id_comp sY') p
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (c p)) := by
  subst hs
  rfl

/-! ### The class `c'_p(Q)` -/

/-- The section at zero followed by the projection to `X` and the structure morphism is `f`. -/
private theorem modificationSectionAtZero_comp_projection_comp_structure
    (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (b : W ⟶ projectiveLineProduct f) [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫
      modificationProjection f b ≫ f = f := by
  rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp]

section Modification

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

/-- **The class `P'_p(Q)` of Stacks 0F9K.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over
`𝐀¹_X`, let `Z ⊆ X` be closed, let `Q ∈ D(𝒪_W)` have defined Chern classes, and let `T ⊆ W_∞` be
closed, contain every point of `W_∞` over `X ∖ Z`, and be such that `Q|_T` is zero. The class is
`(E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`, where `E = W_∞ ×_X Z`, `P'_p(Q|_E)` is the extension
of `P_p(Q)|_E` along the closed cover `W_∞ = T ∪ E`, and `C` is the class of Stacks 0F9J
(`Stacks.Chow.gysinAtInfinityData`). -/
@[stacks 0F9K "the class P'_p(Q) in A^p(Z ⟶ X), for Q|_T zero"]
def modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  localizedModificationClass (gysinAtInfinityData C f b hA) z t hT
    (vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hzero)

/-- **The class `c'_p(Q)` of Stacks 0F9K.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over
`𝐀¹_X`, let `Z ⊆ X` be closed, let `Q ∈ D(𝒪_W)` have defined Chern classes, and let `T ⊆ W_∞` be
closed, contain every point of `W_∞` over `X ∖ Z`, and be such that `Q|_T` is finite locally free
of rank `< p` in degree `0`. The class is `(E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`, where
`E = W_∞ ×_X Z`, `c'_p(Q|_E)` is the extension of `c_p(Q)|_E` along the closed cover
`W_∞ = T ∪ E`, and `C` is the class of Stacks 0F9J (`Stacks.Chow.gysinAtInfinityData`). -/
@[stacks 0F9K "the class c'_p(Q) in A^p(Z ⟶ X), for Q|_T finite locally free of rank < p in \
degree 0"]
def modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  localizedModificationClass (gysinAtInfinityData C f b hA) z t hT
    (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank)

/-- In the situation of `Stacks.Chow.modificationPowerSum`,
`(Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})` in `A^p(X)`, where `(Z ⟶ X)_* ∘ -` is the pushforward
of Stacks 0EPK and `Q|_{X × {0}}` is the derived pullback of `Q` along the section at zero
`i_0 : X ⟶ W`. -/
@[stacks 0F9K "the case of P'_p: (Z ⟶ X)_* ∘ P'_p(Q) = P_p(Q|_{X × {0}})"]
theorem properPushforwardChowCohomology_modificationPowerSum
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    properPushforwardChowCohomology C f (z ≫ f) z rfl
        (modificationPowerSum C f b hA z t hQ p hT hzero) =
      perfectPowerSumComponent C f (hQ.derivedPullback
        (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) p := by
  have hs := modificationSectionAtZero_comp_projection_comp_structure C f b hA
  have hres : TotalChowClass.res _ hs
      (perfectPowerSum C (modificationProjection f b ≫ f) hQ p) =
      perfectPowerSum C f (hQ.derivedPullback _) p :=
    res_perfectPowerSum_derivedPullback C _ hQ _ hs _ p
  show _ = perfectPowerSum C f (hQ.derivedPullback _) p p
  rw [← hres, TotalChowClass.res_apply_eq_bivariantClassCongrBase]
  exact properPushforwardChowCohomology_localizedModificationClass (gysinAtInfinityData C f b hA)
    z t hT (vanishesOver_perfectPowerSumClass_of_isZero C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hzero)

/-- In the situation of `Stacks.Chow.modificationChernClass`,
`(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})` in `A^p(X)`, where `(Z ⟶ X)_* ∘ -` is the pushforward
of Stacks 0EPK and `Q|_{X × {0}}` is the derived pullback of `Q` along the section at zero
`i_0 : X ⟶ W`. -/
@[stacks 0F9K "the case of c'_p: (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})"]
theorem properPushforwardChowCohomology_modificationChernClass
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    properPushforwardChowCohomology C f (z ≫ f) z rfl
        (modificationChernClass C f b hA z t hQ p hT hrank) =
      perfectChernClass C f (hQ.derivedPullback
        (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) p := by
  have hs := modificationSectionAtZero_comp_projection_comp_structure C f b hA
  have hres : TotalChowClass.res _ hs (perfectChernClass C (modificationProjection f b ≫ f) hQ) =
      perfectChernClass C f (hQ.derivedPullback _) :=
    res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ _ hs _
  rw [← hres, TotalChowClass.res_apply_eq_bivariantClassCongrBase]
  exact properPushforwardChowCohomology_localizedModificationClass (gysinAtInfinityData C f b hA)
    z t hT (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
      (t ≫ modificationInclusionAtInfinity f b) hQ p hrank)

end Modification

end Stacks.Chow

end
