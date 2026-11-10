module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.PreparationNewton
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BivariantCommute

/-!
# The Whitney formula for the classes `c^{(p)}(Q)` of Stacks 0F9K

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, with fibre at infinity `W_∞` and section at zero `i_0 : X ⟶ W`, and let
`T ⊆ W_∞` be a closed subscheme containing every point of `W_∞` lying over `X ∖ Z`. For
`Q ∈ D(𝒪_W)` with defined Chern classes such that `Q|_T` is isomorphic to a finite locally free
module of rank `< p` placed in degree `0`, Stacks 0FAY considers the element

  `c^{(p)}(Q) = 1 + c_1(Q|_{X × {0}}) + … + c_{p-1}(Q|_{X × {0}}) + c'_p(Q) + c'_{p+1}(Q) + …`

of the group `A^{(p)}(Z ⟶ X)` of Stacks 0FA0, with `c'_i(Q) ∈ A^i(Z ⟶ X)` the classes of
Stacks 0F9K, and states the Whitney formula `c^{(p+p')}(Q ⊕ Q') = c^{(p)}(Q) c^{(p')}(Q')` for
the multiplication of Stacks 0FA0 (`Stacks.Chow.localizedGradingMul`).

## The proof

Below the cutoff `p + p'`, the pushed components of `c^{(p)}(Q)` are the Chern classes of
`Q|_{X × {0}}` (Stacks 0F9K), and the components agree by the Whitney formula on `X`. From the
cutoff on, every component of either side is the localized class `q'` of a class `q ∈ A^n(W)`
vanishing over `T` (`Stacks.Chow.IsLocalizedModificationClass`): the left side is the localized
class of `c_n(Q ⊕ Q') = ∑ c_i(Q) c_{n-i}(Q')`, and the summands of the right side are the
localized classes of the summands `c_i(Q) c_{n-i}(Q')`. There are three kinds of summands:

* `i ≥ p`, `n - i ≥ p'`: the third multiplication of Stacks 0FA0, by Stacks 0FA1 and 0FAV
  (`Stacks.Chow.IsLocalizedModificationClass.supportedMul`);
* `i ≥ p`, `n - i < p'`: the first multiplication, `c'_i(Q) ∘ c_{n-i}(Q'|_{X × {0}})`, where
  `c_{n-i}(Q'|_{X × {0}}) = i_0^* c_{n-i}(Q')` and the class at infinity of Stacks 0F9J commutes
  with `i_0^*` (Stacks 0FAV);
* `i < p`: the second multiplication, `res(c_i(Q|_{X × {0}})) ∘ c'_{n-i}(Q')`, which is
  `c'_{n-i}(Q') ∘ c_i(Q|_{X × {0}})` since bivariant classes commute with Chern classes
  (Stacks 0FAC); this is the previous case with the factors exchanged, and
  `c_{n-i}(Q') c_i(Q) = c_i(Q) c_{n-i}(Q')` in `A^*(W)`, Chern classes being central.

## Main definitions

* `Stacks.Chow.modificationTotalChernClass` — the class `c^{(p)}(Q) ∈ A^{(p)}(Z ⟶ X)`.

## Main results

* `Stacks.Chow.modificationTotalChernClass_biprod` — **Stacks 0FAY**.
* `Stacks.Chow.ambientSupportedMul_perfectChernClass_heq` — the second multiplication of
  Stacks 0FA0 by a Chern class `c_k(E)` is the first one, `res(c_k(E)) ∘ c = c ∘ c_k(E)`.
* `Stacks.Chow.IsLocalizedModificationClass.supportedRightComp` — the first multiplication of
  Stacks 0FA0 on localized classes: `q' ∘ i_0^* d = (q d)'`.
* `Stacks.Chow.localizedGradingPush_modificationTotalChernClass` — the pushed components of
  `c^{(p)}(Q)` are the Chern classes of `Q|_{X × {0}}` (Stacks 0F9K).

## Implementation notes

The source assumes `Q` and `Q'` perfect; only the definedness of their Chern classes is used, so
perfectness is not assumed (as in `Stacks.Chow.modificationChernClass`). The hypothesis of
Stacks 0F9K on `(Q ⊕ Q')|_T`, of rank `< p + p'`, is derived from those on `Q|_T` and `Q'|_T`
(`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod`), and the definedness of
the Chern classes of `Q ⊕ Q'` from those of `Q` and `Q'`
(`Stacks.Chow.hasDefinedChernClasses_biprod`).

## References

* [Stacks Project, Tag 0FAY](https://stacks.math.columbia.edu/tag/0FAY)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0FAV](https://stacks.math.columbia.edu/tag/0FAV)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Chern classes of a derived pullback, componentwise -/

section Pullback

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY'] (g : Y' ⟶ Y) [LocallyOfFiniteType g]
  (hs : g ≫ sY = sY') {E : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E)

/-- The Chern class `c_k(Lg^*E)` is the restriction `g^* c_k(E)` of Stacks 0B7F, read against the
structure morphism `sY'` of the source. -/
theorem perfectChernClass_derivedPullback_apply (k : ℕ) :
    perfectChernClass C sY' (hE.derivedPullback g) k =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y') hs hs
        (hv := Category.id_comp _) (hv' := Category.id_comp sY') k
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY g k
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (perfectChernClass C sY hE k)) := by
  rw [← res_perfectChernClass_derivedPullback_of_comp_eq C sY hE g hs (hE.derivedPullback g),
    TotalChowClass.res_apply_eq_bivariantClassCongrBase]

/-- The Chern class `c_k(Lg^*E)` in an integer degree `k` is the restriction `g^* c_k(E)` of
Stacks 0B7F, read against the structure morphism `sY'` of the source. -/
theorem intComponent_perfectChernClass_derivedPullback (k : ℤ) :
    (perfectChernClass C sY' (hE.derivedPullback g)).intComponent C sY' k =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y') hs hs
        (hv := Category.id_comp _) (hv' := Category.id_comp sY') k
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY g k
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          ((perfectChernClass C sY hE).intComponent C sY k)) := by
  rcases lt_or_ge k 0 with hk | hk
  · exact (chowCohomologyComponent_eq_zero_of_neg C _ sY' hk _).trans
      (chowCohomologyComponent_eq_zero_of_neg C _ sY' hk _).symm
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [TotalChowClass.intComponent_natCast, TotalChowClass.intComponent_natCast,
      perfectChernClass_derivedPullback_apply C g hs hE m]

end Pullback

/-! ### The second multiplication of Stacks 0FA0 by a Chern class -/

section Ambient

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [LocallyOfFiniteType f]
  (hf : f ≫ sX = sZ) {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)

/-- **The second multiplication of Stacks 0FA0 by a Chern class is the first one.** For
`c ∈ A^q(Z ⟶ X)` and a Chern class `c_k(E) ∈ A^k(X)`, `res(c_k(E)) ∘ c = c ∘ c_k(E)`: by
Stacks 0FAC, `c ∘ c_k(E) = c_k(Lf^*E) ∘ c`, and `c_k(Lf^*E) = res(c_k(E))`. The two sides lie in
`A^{k+q}(Z ⟶ X)` and `A^{q+k}(Z ⟶ X)`. -/
theorem ambientSupportedMul_perfectChernClass_heq (k : ℕ) {q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    ambientSupportedMul C sZ sX f hf (perfectChernClass C sX hE k) c ≍
      supportedRightComp C sZ sX f hf c (perfectChernClass C sX hE k) := by
  unfold ambientSupportedMul supportedRightComp supportedLeftComp
  refine (BivariantClass.congrHom_heq _ _ _).trans
    (HEq.trans ?_ (BivariantClass.congrHom_heq _ _ _).symm)
  have h := c.heq_bivariantCompositeOfInvertible_perfectChernClass hE k
  rw [perfectChernClass_derivedPullback_apply C f hf hE k] at h
  exact h.symm

end Ambient

/-! ### The first multiplication of Stacks 0FA0 on localized classes -/

section Localized

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  {D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA}
  {z : Z ⟶ X} [IsClosedImmersion z] {t : T ⟶ modificationFibreAtInfinity f b}
  [IsClosedImmersion t]
  {hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t} {p r : ℤ}

/-- **Localized classes, composed with a restriction to the section at zero**, by the first
multiplication of Stacks 0FA0, when the class at infinity commutes with `d`: if `c = q'` then
`c ∘ i_0^* d = (q d)'`. -/
theorem IsLocalizedModificationClass.supportedRightComp
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    (h : IsLocalizedModificationClass D z t hT q c)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r)
    (hd : CommutesAtInfinity D d) :
    IsLocalizedModificationClass D z t hT (q.mulId C _ d)
      (Stacks.Chow.supportedRightComp C (z ≫ f) f z rfl c
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 X)
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (by rw [← Category.assoc, D.sectionAtZero_comp, Category.id_comp])
          (hv := Category.id_comp _) (hv' := Category.id_comp f) r
          (chowCohomologyRestriction C (gysinSystemOfInvertible C)
            (modificationProjection f b ≫ f) (modificationSectionAtZero f b D.isIsoFibreAtZero) r
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d))) := by
  obtain ⟨hq, rfl⟩ := h
  exact ⟨_, localizedModificationClass_supportedRightComp_of_heq D z t hT hq d hd⟩

/-- Being a localized class is invariant under heterogeneous equality of both classes, over an
equality of degrees. -/
theorem IsLocalizedModificationClass.of_heq (hpr : p = r)
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {c : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p}
    {q' : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) r}
    {c' : BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl r}
    (h : IsLocalizedModificationClass D z t hT q c) (hq : q ≍ q') (hc : c ≍ c') :
    IsLocalizedModificationClass D z t hT q' c' := by
  subst hpr
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq hc
  exact h

end Localized

/-! ### The class `c^{(p)}(Q)` and Stacks 0FAY -/

section Whitney

variable (C : ChowSituation.{u}) {X W Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q)

/-- **The class `c^{(p)}(Q) ∈ A^{(p)}(Z ⟶ X)` of Stacks 0FAY.** In the situation of Stacks 0F9K
(`Stacks.Chow.modificationChernClass`), with `Q|_T` isomorphic to a finite locally free module of
rank `< p` placed in degree `0`,

  `c^{(p)}(Q) = 1 + c_1(Q|_{X × {0}}) + … + c_{p-1}(Q|_{X × {0}}) + c'_p(Q) + c'_{p+1}(Q) + …`:

its component in a degree `0 ≤ i < p` is `c_i(Q|_{X × {0}}) ∈ A^i(X)`, with `Q|_{X × {0}}` the
derived pullback along the section at zero, in a negative degree it is `0`, and in a degree
`i ≥ p` it is the class `c'_i(Q) ∈ A^i(Z ⟶ X)` of Stacks 0F9K, which is defined since a rank
`< p` is a rank `< i`. -/
@[stacks 0FAY "the class c^(p)(Q) in A^(p)(Z → X)"]
def modificationTotalChernClass (p : ℕ)
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  (fun i => TotalChowClass.intComponent C f (perfectChernClass C f (hQ.derivedPullback
      (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)))) i.1,
    fun i => bivariantClassDegreeCongr C _ (z ≫ f) f z rfl
      (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg p) i.2))
      (modificationChernClass C f b hA z t hQ i.1.toNat hT
        (hrank.imp fun _ hM => ⟨hM.1.mono (by have := i.2; omega), hM.2⟩)))

variable {C f b hA z t hQ} {p : ℕ}
  {hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t}

/-- The components of `c^{(p)}(Q)` below the cutoff are the Chern classes of `Q|_{X × {0}}`. -/
theorem modificationTotalChernClass_fst
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (i : {i : ℤ // i < (p : ℤ)}) :
    (modificationTotalChernClass C f b hA z t hQ p hT hrank).1 i =
      TotalChowClass.intComponent C f (perfectChernClass C f (hQ.derivedPullback
        (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)))) i.1 :=
  rfl

/-- **The components of `c^{(p)}(Q)` from the cutoff on are localized classes**: in a degree
`i ≥ p` the component `c'_i(Q)` is the localized class of `c_i(Q) ∈ A^i(W)` (Stacks 0F9K). -/
theorem isLocalizedModificationClass_modificationTotalChernClass_snd
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (i : {i : ℤ // (p : ℤ) ≤ i}) :
    IsLocalizedModificationClass (gysinAtInfinityData C f b hA) z t hT
      ((perfectChernClass C (modificationProjection f b ≫ f) hQ).intComponent C _ i.1)
      ((modificationTotalChernClass C f b hA z t hQ p hT hrank).2 i) := by
  rw [TotalChowClass.intComponent, dite_eq_left (le_trans (Int.natCast_nonneg p) i.2)]
  exact IsLocalizedModificationClass.bivariantClassDegreeCongr _
    (IsLocalizedModificationClass.of_vanishesOver
      (vanishesOver_perfectChernClass_of_rankLT C (modificationProjection f b ≫ f)
        (t ≫ modificationInclusionAtInfinity f b) hQ _
        (hrank.imp fun _ hM => ⟨hM.1.mono (by have := i.2; omega), hM.2⟩)))

/-- **The pushed components of `c^{(p)}(Q)` are the Chern classes of `Q|_{X × {0}}`**: in a
degree `i ≥ p`, `(Z ⟶ X)_* ∘ c'_i(Q) = c_i(Q|_{X × {0}})` by Stacks 0F9K. -/
theorem localizedGradingPush_modificationTotalChernClass
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) (i : ℤ) :
    localizedGradingPush C (z ≫ f) f z rfl (modificationTotalChernClass C f b hA z t hQ p hT hrank)
        i =
      TotalChowClass.intComponent C f (perfectChernClass C f (hQ.derivedPullback
        (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)))) i := by
  rcases lt_or_ge i (p : ℤ) with h | h
  · rw [localizedGradingPush_of_lt _ h]
    rfl
  · rw [localizedGradingPush_of_le _ h]
    change properPushforwardChowCohomology C f (z ≫ f) z rfl
      (bivariantClassDegreeCongr C _ (z ≫ f) f z rfl _ _) = _
    rw [properPushforwardChowCohomology_bivariantClassDegreeCongr,
      properPushforwardChowCohomology_modificationChernClass, TotalChowClass.intComponent,
      dite_eq_left (by omega)]

variable {Q' : DerivedCategory W.Modules} (hQ' : HasDefinedChernClasses Q') {p' : ℕ}

/-- In the situation of Stacks 0F9K, let `Q, Q' ∈ D(𝒪_W)` have defined Chern classes, with `Q|_T`
and `Q'|_T` isomorphic to finite locally free modules of ranks `< p` and `< p'` placed in degree
`0`. Then

  `c^{(p+p')}(Q ⊕ Q') = c^{(p)}(Q) c^{(p')}(Q')`   in `A^{(p+p')}(Z ⟶ X)`,

with the classes of `Stacks.Chow.modificationTotalChernClass` and the multiplication of
Stacks 0FA0 (`Stacks.Chow.localizedGradingMul`). The hypothesis on `(Q ⊕ Q')|_T`, under which
`c^{(p+p')}(Q ⊕ Q')` is defined, follows from those on `Q|_T` and `Q'|_T`
(`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod`), and so does the
definedness of the Chern classes of `Q ⊕ Q'` (`Stacks.Chow.hasDefinedChernClasses_biprod`).
Perfectness of `Q`, `Q'` is not used, only that their Chern classes are defined. -/
@[stacks 0FAY "c^(p+p')(Q ⊕ Q') = c^(p)(Q) c^(p')(Q') in A^(p+p')(Z → X), with the \
multiplication of 0FA0"]
theorem modificationTotalChernClass_biprod
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank' : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p' ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q' ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    modificationTotalChernClass C f b hA z t (hasDefinedChernClasses_biprod hQ hQ') (p + p') hT
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod _ hrank hrank') =
      localizedGradingMul C (z ≫ f) f z rfl
        (modificationTotalChernClass C f b hA z t hQ p hT hrank)
        (modificationTotalChernClass C f b hA z t hQ' p' hT hrank') := by
  have hEF := hasDefinedChernClasses_biprod hQ hQ'
  have hs : modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫
      modificationProjection f b ≫ f = f := by
    rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp]
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · -- Below the cutoff: the Whitney formula on `X`, through Stacks 0F9K.
    have hX : perfectChernClass C f (hEF.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) =
        perfectChernClass C f (hQ.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) *
        perfectChernClass C f (hQ'.derivedPullback
          (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))) := by
      rw [← res_perfectChernClass_derivedPullback_of_comp_eq C _ hEF _ hs,
        perfectChernClass_biprod C _ hQ hQ' hEF, map_mul,
        res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ _ hs,
        res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ' _ hs]
    rw [localizedGradingMul_fst, modificationTotalChernClass_fst, hX,
      TotalChowClass.intComponent_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [localizedGradingPush_modificationTotalChernClass,
      localizedGradingPush_modificationTotalChernClass]
  · -- From the cutoff on: both sides are localized classes of `c_n(Q ⊕ Q')`.
    have hn := n.2
    push_cast at hn
    have key : IsLocalizedModificationClass (gysinAtInfinityData C f b hA) z t hT
        ((perfectChernClass C (modificationProjection f b ≫ f) hEF).intComponent C _ n.1)
        ((localizedGradingMul C (z ≫ f) f z rfl
          (modificationTotalChernClass C f b hA z t hQ p hT hrank)
          (modificationTotalChernClass C f b hA z t hQ' p' hT hrank')).2 n) := by
      rw [perfectChernClass_biprod C _ hQ hQ' hEF, TotalChowClass.intComponent_mul,
        localizedGradingMul_snd]
      refine IsLocalizedModificationClass.sum _ fun i hi => ?_
      have hi' := Finset.mem_Icc.mp hi
      refine IsLocalizedModificationClass.bivariantClassDegreeCongr _ ?_
      by_cases hpi : (p : ℤ) ≤ i
      · by_cases hqi : (p' : ℤ) ≤ n.1 - i
        · rw [localizedGradingHighTerm_of_le_of_le _ _ _ hpi hqi]
          exact (isLocalizedModificationClass_modificationTotalChernClass_snd hrank
            ⟨i, hpi⟩).supportedMul
            (isLocalizedModificationClass_modificationTotalChernClass_snd hrank' ⟨n.1 - i, hqi⟩)
            (commutesAtInfinity_gysinAtInfinityData C f b hA _)
        · rw [localizedGradingHighTerm_of_le_of_lt _ _ _ hpi (not_le.mp hqi),
            modificationTotalChernClass_fst,
            intComponent_perfectChernClass_derivedPullback C _ hs hQ']
          exact (isLocalizedModificationClass_modificationTotalChernClass_snd hrank
            ⟨i, hpi⟩).supportedRightComp _ (commutesAtInfinity_gysinAtInfinityData C f b hA _)
      · have hqi : (p' : ℤ) ≤ n.1 - i := by omega
        rw [localizedGradingHighTerm_of_lt _ _ _ (not_le.mp hpi) hqi,
          modificationTotalChernClass_fst]
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi'.1
        rw [TotalChowClass.intComponent_natCast, TotalChowClass.intComponent_natCast]
        refine ((isLocalizedModificationClass_modificationTotalChernClass_snd hrank'
          ⟨n.1 - m, hqi⟩).supportedRightComp _
            (commutesAtInfinity_gysinAtInfinityData C f b hA
              (perfectChernClass C (modificationProjection f b ≫ f) hQ m))).of_heq
          (add_comm _ _) (BivariantClass.heq_mulId_perfectChernClass _ hQ m) ?_
        rw [← perfectChernClass_derivedPullback_apply C _ hs hQ m]
        exact (ambientSupportedMul_perfectChernClass_heq C (z ≫ f) f z rfl _ m _).symm
    obtain ⟨hv, hH⟩ := key
    rw [hH]
    exact (isLocalizedModificationClass_modificationTotalChernClass_snd _ n).eq hv

end Whitney

end Stacks.Chow

end
