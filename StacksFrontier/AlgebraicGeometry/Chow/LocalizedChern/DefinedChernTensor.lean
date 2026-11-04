module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedProductRestriction

/-!
# Localized classes of a derived tensor product: reduction to an envelope

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S`, `Z₁, Z₂ ⊆ X`
closed subschemes and `F₁, F₂ ∈ D(𝒪_X)` perfect objects with `F_i|_{X ∖ Z_i}` zero. Then
`F₁ ⊗^L F₂` is zero on `X ∖ (Z₁ ∩ Z₂)`, where `Z₁ ∩ Z₂ = Z₁ ×_X Z₂`: at every point of the
complement one of the two derived fibres vanishes. When the Chern classes of `F₁` and `F₂` are
defined, so are those of `F₁ ⊗^L F₂`, and Remark 0GUK gives localized classes
`P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` and `c_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)`.

Lemma 0FBF expresses these classes through those of `F₁` and `F₂`. This file carries out the
reduction of such identities to an envelope `g : Y ⟶ X` on which `Lg^*F₁`, `Lg^*F₂` and
`Lg^*(F₁ ⊗^L F₂)` are represented by locally bounded complexes of finite locally free modules:
there the three objects satisfy alternative (c) of condition (3) of Situation 0GUJ. Restriction
along `g` is injective (Stacks 0GUC), it takes the classes of Remark 0GUK to the classes of
Stacks 0FB2 for the base changes
(`Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum`),
and it commutes with the products of classes supported on closed subschemes
(`Stacks.Chow.bivariantRestriction_supportedIntersectionMul`). So an identity of the shape of
Lemma 0FBF holds on `X` as soon as it holds on `Y` for the base-changed data.

## Main definitions

* `Stacks.Chow.LocalizedChernData.ofIsZero` — the data `(X, Z, F)` of a localized class for `F`
  zero away from `Z`, in a given degree.
* `Stacks.Chow.LocalizedChernData.derivedTensorOfIsZero` — the data `(X, Z₁ ∩ Z₂, F₁ ⊗^L F₂)`.
* `Stacks.Chow.supportedOfLocallyConstant` — the class in `A^0(Z ⟶ X)` of a locally constant
  function on `X` vanishing off `Z`.
* `Stacks.Chow.LocalizedChernData.rankChoose` — the class `C(r, n) ∈ A^0(Z ⟶ X)` for
  `r = P_0(Z ⟶ X, E)`.

## Main results

* `Stacks.Chow.isZero_derivedTensor_compl_pullback` — `F₁ ⊗^L F₂` is zero away from `Z₁ ∩ Z₂`.
* `Stacks.Chow.localizedPowerSum_derivedTensor_of_isEnvelope` — the formula for
  `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` of Lemma 0FBF holds once it holds after base change to an envelope
  on which the three objects are represented by complexes of finite locally free modules.
* `Stacks.Chow.localizedChern_one_derivedTensor_of_isEnvelope`,
  `Stacks.Chow.localizedChern_two_derivedTensor_of_isEnvelope` — the same for
  `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` and `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)`.
* `Stacks.Chow.EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree` — on the envelope of
  a presentation the object is represented by a locally bounded complex of finite locally free
  modules.
* `Stacks.Chow.LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_rankChoose` —
  `C(r, n)` restricts to `C(r, n)` of the base change.

## Implementation notes

The proof of Lemma 0FBF in the source reduces, through Lemma 0FE8, to a modification on which the
objects `Q_i` are fixed; the reduction here is the analogous step for the classes of Remark 0GUK,
which are defined through envelopes. The classes upstairs are those of Stacks 0FB2 for the
situations `(Y, Z_i ×_X Y, Lg^*F_i)`, read through `Stacks.Chow.bivariantClassCongrBase`.

The rank `r(E) = P_0(E)` of a perfect object need not be constant, so the binomial coefficient
`C(r_i, 2)` in the formula for `c_2` is read as in Stacks 0FAG and Stacks 0FE5: `r(E)` is the class
of the locally constant function `χ_E : x ↦ χ(E ⊗^L κ(x))`, and `C(r, n)` is the class of
`x ↦ C(χ_E(x), n)`. For `E|_{X ∖ Z}` zero this function vanishes off `Z`, and its class lies in
`A^0(Z ⟶ X)`: it is the extension, along the closed cover of `X` by `Z` and the open and closed
subscheme where the function vanishes (Stacks 0F9H), of the restriction to `Z` of the class of the
function (`Stacks.Chow.LocalizedChernData.rankChoose`). The term `(r₁ r₂ - 1) c₁ c₁'` is read as
`(r₁ r₂)(c₁ c₁') - c₁ c₁'`, as in Stacks 0FE5.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FAG](https://stacks.math.columbia.edu/tag/0FAG)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A derived tensor product vanishes over the union of two opens on which its factors vanish.**
Let `E`, `E'` be perfect with `E|_{U₁}` and `E'|_{U₂}` zero. Then `E ⊗^L E'` restricts to zero
along every morphism with image in `U₁ ∪ U₂`: at every point one of the two derived fibres
vanishes. -/
theorem isZero_derivedPullback_derivedTensor_of_range_subset_opens {V X : Scheme.{u}}
    (U₁ U₂ : X.Opens) {E E' : DerivedCategory X.Modules}
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectE' : RingedSpace.IsPerfect.{u, u + 1} E')
    (hzero : IsZero ((derivedPullback U₁.ι.toLRSHom.toShHom).obj E))
    (hzero' : IsZero ((derivedPullback U₂.ι.toLRSHom.toShHom).obj E'))
    (t : V ⟶ X) (ht : Set.range t ⊆ (U₁ : Set X) ∪ U₂) :
    IsZero ((derivedPullback t.toLRSHom.toShHom).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj E')) := by
  have hT : RingedSpace.IsPerfect.{u, u + 1}
      (((derivedTensorProductFunctor X.sheaf).obj E).obj E') :=
    RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace E E' perfectE perfectE'
  refine isZero_of_forall_isZero_derivedPullback_fromSpecResidueField _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback t.toLRSHom.toShHom _ hT)
    fun v ↦ ?_
  refine IsZero.of_iso ?_ ((derivedPullback (V.fromSpecResidueField v).toLRSHom.toShHom).mapIso
    (derivedPullbackDerivedTensorIso t E E') ≪≫
      derivedPullbackDerivedTensorIso (V.fromSpecResidueField v) _ _)
  have hφ : Set.range (V.fromSpecResidueField v ≫ t) ⊆ {t v} := by
    rintro _ ⟨w, rfl⟩
    simp
  rcases ht ⟨v, rfl⟩ with h | h
  · refine isZero_derivedTensor_of_isZero_left (isZero_derivedPullback_of_isZero_of_comp_eq
      (IsOpenImmersion.lift_fac U₁.ι (V.fromSpecResidueField v ≫ t) ?_) hzero) _
    rw [Scheme.Opens.range_ι]
    exact hφ.trans (Set.singleton_subset_iff.2 h)
  · refine isZero_derivedTensor_of_isZero_right _ (isZero_derivedPullback_of_isZero_of_comp_eq
      (IsOpenImmersion.lift_fac U₂.ι (V.fromSpecResidueField v ≫ t) ?_) hzero')
    rw [Scheme.Opens.range_ι]
    exact hφ.trans (Set.singleton_subset_iff.2 h)

/-! ### The common envelope of two presentations -/

section Presentation

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- On the envelope `f : Y ⟶ X` of a presentation of `E`, the object `Lf^*E` is represented by a
locally bounded complex of finite locally free modules. -/
theorem EnvelopePresentation.exists_isLocallyBoundedFiniteLocallyFree
    (H : EnvelopePresentation E) :
    ∃ P : CochainComplex (OXMod.{u, u, u} H.Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅
          (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            H.f.toLRSHom.toShHom).obj E) :=
  ⟨H.P, H.locallyBounded, ⟨H.representation.some.symm⟩⟩

end Presentation

/-! ### The class of a locally constant function supported on a closed subscheme -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **Restriction of the class of a locally constant function.** Along `h : Y ⟶ X` the class of
`n` restricts to the class of `n ∘ h`. -/
theorem res_ofLocallyConstant_comap (h : Y ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sY)
    (n : LocallyConstant X ℤ) :
    res h hs (ofLocallyConstant C sX n) = ofLocallyConstant C sY (n.comap h.base.hom) := by
  refine eq_of_res_eq (isClopenDecomposition_levelSets (n.comap h.base.hom)) fun j ↦ ?_
  have hk : ∀ y : (levelSets (n.comap h.base.hom) j : Scheme.{u}),
      n (((levelSets (n.comap h.base.hom) j).ι ≫ h).base y) = j.down := fun y ↦ y.2
  have hk' : ∀ y : (levelSets (n.comap h.base.hom) j : Scheme.{u}),
      (n.comap h.base.hom) ((levelSets (n.comap h.base.hom) j).ι.base y) = j.down := fun y ↦ y.2
  rw [res_res, res_ofLocallyConstant _ _ _ j.down hk, res_ofLocallyConstant _ _ _ j.down hk']

end TotalChowClass

section SupportedLocallyConstant

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hi : i ≫ sX = sZ)

/-- The open and closed subscheme on which a locally constant function vanishes is a closed
subscheme. -/
theorem isClosedImmersion_levelSets_zero_ι (n : LocallyConstant X ℤ) :
    IsClosedImmersion (TotalChowClass.levelSets n (ULift.up 0)).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact n.isLocallyConstant.isClosed_fiber _)

variable {i} in
omit [IsClosedImmersion i] in
/-- A locally constant function vanishing off `Z`: `X` is the union of `Z` and the open and closed
subscheme on which the function vanishes. -/
theorem range_levelSets_zero_union_eq_univ {n : LocallyConstant X ℤ}
    (hn : ∀ x, x ∉ Set.range i → n x = 0) :
    Set.range (TotalChowClass.levelSets n (ULift.up 0)).ι ∪ Set.range i = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ (em (x ∈ Set.range i)).elim Or.inr fun hx ↦
    Or.inl (by rw [Scheme.Opens.range_ι]; exact hn x hx)

variable {i sZ} in
/-- The class of a locally constant function, restricted to `Z`, vanishes over the part of `Z`
lying in a closed subscheme on which the function vanishes. -/
theorem vanishesOver_res_ofLocallyConstant_of_eq {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    [IsClosedImmersion i₁] (hi : i ≫ sX = sZ) {n : LocallyConstant X ℤ}
    (hn : ∀ y : X₁, n (i₁.base y) = 0) :
    BivariantClass.VanishesOver (TotalChowClass.res i hi (TotalChowClass.ofLocallyConstant C sX
      n) 0) (pullback.snd i₁ i) := by
  subst hi
  exact vanishesOver_res_ofLocallyConstant C sX i n hn

/-- **The class in `A^0(Z ⟶ X)` of a locally constant function `n` on `X` vanishing off `Z`**:
the extension (Stacks 0F9H) along the closed cover of `X` by `Z` and the open and closed subscheme
`{n = 0}` of the restriction to `Z` of the class of `n`. It is the extension along every closed
cover `X = X₁ ∪ Z` with `n` zero on `X₁`
(`Stacks.Chow.supportedOfLocallyConstant_eq_closedCoverExtension`). -/
def supportedOfLocallyConstant (n : LocallyConstant X ℤ) (hn : ∀ x, x ∉ Set.range i → n x = 0) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi ((0 : ℕ) : ℤ) :=
  haveI := isClosedImmersion_levelSets_zero_ι n
  closedCoverExtension C sX (TotalChowClass.levelSets n (ULift.up 0)).ι i sZ hi
    (TotalChowClass.res i hi (TotalChowClass.ofLocallyConstant C sX n) 0)
    (range_levelSets_zero_union_eq_univ hn)
    (vanishesOver_res_ofLocallyConstant_of_eq C sX (TotalChowClass.levelSets n (ULift.up 0)).ι hi
      fun y ↦ y.2)

/-- `Stacks.Chow.supportedOfLocallyConstant` is the extension of the restriction of the class of
`n` along every closed cover `X = X₁ ∪ Z` with `n` zero on `X₁` (Stacks 0FAH). -/
theorem supportedOfLocallyConstant_eq_closedCoverExtension (n : LocallyConstant X ℤ)
    (hn : ∀ x, x ∉ Set.range i → n x = 0) {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁]
    (hcover : Set.range i₁ ∪ Set.range i = Set.univ) (h₁ : ∀ y : X₁, n (i₁.base y) = 0) :
    supportedOfLocallyConstant C sX i sZ hi n hn =
      closedCoverExtension C sX i₁ i sZ hi
        (TotalChowClass.res i hi (TotalChowClass.ofLocallyConstant C sX n) 0) hcover
        (vanishesOver_res_ofLocallyConstant_of_eq C sX i₁ hi h₁) := by
  have := isClosedImmersion_levelSets_zero_ι n
  exact closedCoverExtension_eq_of_closedCover C sX _ i₁ i sZ hi
    (range_levelSets_zero_union_eq_univ hn) hcover
    (vanishesOver_res_ofLocallyConstant_of_eq C sX (TotalChowClass.levelSets n (ULift.up 0)).ι hi
      fun y ↦ y.2) _

/-- `Stacks.Chow.supportedOfLocallyConstant` only depends on the function. -/
theorem supportedOfLocallyConstant_congr {n n' : LocallyConstant X ℤ} (e : n = n')
    (hn : ∀ x, x ∉ Set.range i → n x = 0) (hn' : ∀ x, x ∉ Set.range i → n' x = 0) :
    supportedOfLocallyConstant C sX i sZ hi n hn =
      supportedOfLocallyConstant C sX i sZ hi n' hn' := by
  subst e
  rfl

/-- `Stacks.Chow.supportedOfLocallyConstant` read against an equal structure morphism of `Z` is
`Stacks.Chow.supportedOfLocallyConstant` for that structure morphism. -/
theorem bivariantClassCongrBase_supportedOfLocallyConstant {sZ' : Z ⟶ C.S}
    [LocallyOfFiniteType sZ'] (e : sZ = sZ') (hi' : i ≫ sX = sZ') (n : LocallyConstant X ℤ)
    (hn : ∀ x, x ∉ Set.range i → n x = 0) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) i e rfl (hv := hi) (hv' := hi') _
        (supportedOfLocallyConstant C sX i sZ hi n hn) =
      supportedOfLocallyConstant C sX i sZ' hi' n hn := by
  subst e
  rfl

/-- **Restriction of `Stacks.Chow.supportedOfLocallyConstant`** (Stacks 0F9Z) along `h : X' ⟶ X`
is the class of `n ∘ h`, supported on `Z ×_X X'`. -/
theorem bivariantRestriction_supportedOfLocallyConstant {X' : Scheme.{u}} (h : X' ⟶ X)
    [LocallyOfFiniteType h] (n : LocallyConstant X ℤ) (hn : ∀ x, x ∉ Set.range i → n x = 0) :
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi h ((0 : ℕ) : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (supportedOfLocallyConstant C sX i sZ hi n hn) =
      supportedOfLocallyConstant C (h ≫ sX) (pullback.snd i h) (pullback.fst i h ≫ sZ)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi h) (n.comap h.base.hom)
        (fun x hx ↦ hn _ fun ⟨z, hz⟩ ↦ hx (by
          obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
          exact ⟨w, rfl⟩)) := by
  have := isClosedImmersion_levelSets_zero_ι n
  rw [supportedOfLocallyConstant_eq_closedCoverExtension C sX i sZ hi n hn _
    (range_levelSets_zero_union_eq_univ hn) fun y ↦ y.2, bivariantRestriction_closedCoverExtension]
  refine Eq.trans ?_ (supportedOfLocallyConstant_eq_closedCoverExtension C (h ≫ sX)
    (pullback.snd i h) _ _ _ _ (pullback.snd (TotalChowClass.levelSets n (ULift.up 0)).ι h)
    (range_pullbackSnd_union_eq_univ _ _ (range_levelSets_zero_union_eq_univ hn) h)
    fun y ↦ by
      change n ((pullback.snd _ h ≫ h).base y) = 0
      rw [← pullback.condition]
      exact ((pullback.fst _ h).base y).2).symm
  congr 1
  rw [← TotalChowClass.res_ofLocallyConstant_comap h rfl n, ← TotalChowClass.res_rfl_apply,
    TotalChowClass.res_res, TotalChowClass.res_res]
  exact congrFun (TotalChowClass.res_congr pullback.condition _ _ _) _

end SupportedLocallyConstant

/-! ### The class `C(r, n)` of a perfect object zero off a closed subscheme -/

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-- The rank of a perfect object `E` vanishes off a closed subscheme `Z` when `E|_{X ∖ Z}` is
zero, and so do the binomial coefficients `C(χ_E, n)`, `n ≥ 1`. -/
theorem rankChoose_eq_zero_of_isZeroOnComplement (h : D.IsZeroOnComplement) {n : ℕ}
    (hn : 0 < n) (x : D.X) (hx : x ∉ Set.range D.i) :
    (perfectRank D.E D.perfect).map (fun k ↦ Ring.choose k n) x = 0 := by
  have h0 : perfectRank D.E D.perfect x = 0 :=
    perfectRank_eq_zero_of_isZero D.perfect (Scheme.Opens.ι _) h ⟨x, hx⟩
  rw [LocallyConstant.map_apply, Function.comp_apply, h0, Ring.choose_zero_pos ℤ hn]

/-- **The class `C(r, n) ∈ A^0(Z ⟶ X)`** of Stacks 0FBF, for `r = P_0(Z ⟶ X, E)` and `n ≥ 1`,
when `E|_{X ∖ Z}` is zero. The rank `r(E) = P_0(E)` is the class of the locally constant function
`χ_E : x ↦ χ(E ⊗^L κ(x))` (`Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant`), which vanishes
off `Z`; accordingly `C(r, n)` is the class in `A^0(Z ⟶ X)` of the locally constant function
`x ↦ C(χ_E(x), n)`, which vanishes off `Z` as well
(`Stacks.Chow.supportedOfLocallyConstant`). -/
def rankChoose (h : D.IsZeroOnComplement) (n : ℕ) (hn : 0 < n) :
    BivariantClass D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl ((0 : ℕ) : ℤ) :=
  supportedOfLocallyConstant D.base D.a D.i (D.i ≫ D.a) rfl
    ((perfectRank D.E D.perfect).map fun k ↦ Ring.choose k n)
    (D.rankChoose_eq_zero_of_isZeroOnComplement h hn)

/-- **`C(r, n)` restricts along `g : Y ⟶ X` to `C(r, n)` of the base change**, read with the
source over the base through `Y`: the rank of `Lg^*E` is the rank of `E` composed with `g`. -/
theorem bivariantClassCongrBase_bivariantRestriction_rankChoose (h : D.IsZeroOnComplement)
    {Y : Scheme.{u}} (g : Y ⟶ D.X) [LocallyOfFiniteType g] (n : ℕ) (hn : 0 < n) :
    bivariantClassCongrBase D.base (gysinSystemOfInvertible D.base) (pullback.snd D.i g)
        (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl g)
        (hv' := rfl) _
        (bivariantRestriction D.base (gysinSystemOfInvertible D.base) (D.i ≫ D.a) D.a D.i rfl g
          _ (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
          (D.rankChoose h n hn)) =
      (D.pullback g).rankChoose h.pullback n hn := by
  rw [rankChoose, bivariantRestriction_supportedOfLocallyConstant]
  refine (bivariantClassCongrBase_supportedOfLocallyConstant _ _ _ _ _ _ _ _ _).trans
    (supportedOfLocallyConstant_congr _ _ _ _ _ (LocallyConstant.ext fun y ↦ ?_) _ _)
  have hχ := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback g D.E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect D.E D.perfect)) y
  rw [Function.comp_apply] at hχ
  exact congrArg (fun k ↦ Ring.choose k n) hχ.symm

end LocalizedChernData

/-! ### Products of classes supported on one closed subscheme, against equal structure morphisms -/

section SupportedMulCongr

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Z ⟶ X) [IsClosedImmersion f] {p q : ℤ}

/-- The third multiplication of Stacks 0FA0 commutes with reading classes against an equal
structure morphism of `Z`. -/
theorem bivariantClassCongrBase_supportedMul {sZ sZ' : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    [LocallyOfFiniteType sZ'] (e : sZ = sZ') (hf : f ≫ sX = sZ) (hf' : f ≫ sX = sZ')
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) f e rfl (hv := hf) (hv' := hf') (p + q)
        (supportedMul C sZ sX f hf c c') =
      supportedMul C sZ' sX f hf'
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f e rfl (hv := hf) (hv' := hf') p c)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f e rfl (hv := hf) (hv' := hf') q
          c') := by
  subst e
  rfl

end SupportedMulCongr

section Tensor

open Finset


variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
  (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₂]

/-- The data `(X, Z, F)` of a localized Chern class for `F` perfect with `F|_{X ∖ Z}` zero, in a
given degree. -/
abbrev LocalizedChernData.ofIsZero {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : DerivedCategory X.Modules)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
        i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F))
    (p : ℕ) : LocalizedChernData.{u} where
  base := C
  X := X
  a := a
  Z := Z
  i := i
  E := F
  p := p
  perfect := hF
  restriction := Or.inl h

variable {F₁ F₂ : DerivedCategory X.Modules}
  (hF₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₁)
  (hF₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F₂)
  (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₁.base)ᶜ,
        i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₁))
  (h₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i₂.base)ᶜ,
        i₂.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F₂))

include hF₁ hF₂ h₁ h₂ in
/-- `F₁ ⊗^L F₂` is zero away from `Z₁ ∩ Z₂ = Z₁ ×_X Z₂` when `F₁` is zero away from `Z₁` and `F₂`
away from `Z₂`. -/
theorem isZero_derivedTensor_compl_pullback :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range (pullback.snd i₁ i₂ ≫ i₂).base)ᶜ,
        (pullback.snd i₁ i₂ ≫ i₂).isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          X.Opens).isOpenEmbedding)).obj
      (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)) := by
  refine isZero_derivedPullback_derivedTensor_of_range_subset_opens _ _ hF₁ hF₂ h₁ h₂
    (Scheme.Opens.ι _) ?_
  rw [Scheme.Opens.range_ι]
  refine fun x hx ↦ Classical.byContradiction fun hcon ↦ hx ?_
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hcon
  obtain ⟨z₁, hz₁⟩ : x ∈ Set.range i₁ := by simpa using hcon.1
  obtain ⟨z₂, hz₂⟩ : x ∈ Set.range i₂ := by simpa using hcon.2
  obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback z₁ z₂ (hz₁.trans hz₂.symm)
  exact ⟨w, by rw [Scheme.Hom.comp_apply, ← hz₂]⟩

/-- **The data of the localized classes of `F₁ ⊗^L F₂` along `Z₁ ∩ Z₂`**: for `F₁` zero away from
`Z₁` and `F₂` zero away from `Z₂`, the derived tensor product is zero away from the scheme
theoretic intersection `Z₁ ×_X Z₂` (`Stacks.Chow.isZero_derivedTensor_compl_pullback`). -/
abbrev LocalizedChernData.derivedTensorOfIsZero (p : ℕ) : LocalizedChernData.{u} :=
  LocalizedChernData.ofIsZero C a (pullback.snd i₁ i₂ ≫ i₂)
    (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)
    (RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace F₁ F₂ hF₁ hF₂)
    (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p

variable {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g]

/-- A class supported on `W ⟶ X` is determined by its restriction along an envelope `g : Y ⟶ X`. -/
private theorem eq_of_congrBase_restrictionAddHom_eq {W : Scheme.{u}} (iW : W ⟶ X)
    [IsClosedImmersion iW] {p : ℤ} (hg : IsEnvelope g)
    {c d : BivariantClass C (gysinSystemOfInvertible C) (iW ≫ a) a iW rfl p}
    (h : bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd iW g)
        (pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g) (hv' := rfl) p
        (bivariantRestrictionAddHom C (gysinSystemOfInvertible C) (iW ≫ a) a iW rfl g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) =
      bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd iW g)
        (pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g) (hv' := rfl) p
        (bivariantRestrictionAddHom C (gysinSystemOfInvertible C) (iW ≫ a) a iW rfl g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) :
    c = d :=
  bivariantRestrictionAddHom_injective_of_isEnvelope' C _ _ _ _ _ g p _ hg
    ((bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd iW g)
      (pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g).symm rfl
      (hv := pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g) (hv' := rfl) p
      ).injective h)

/-- The restriction along `g` of a product of classes supported on `Z₁` and `Z₂` is the product of
the restrictions, over the pullback square of the base changes. -/
private theorem congrBase_restriction_supportedIntersectionMul {V₁ V₂ W : Scheme.{u}}
    (f₁ : V₁ ⟶ X) [IsClosedImmersion f₁] (f₂ : V₂ ⟶ X) [IsClosedImmersion f₂]
    {w₁ : W ⟶ V₁} {w₂ : W ⟶ V₂} (sq : IsPullback w₁ w₂ f₁ f₂) (iW : W ⟶ X) [IsClosedImmersion iW]
    (hW : w₂ ≫ f₂ = iW) {p q : ℤ}
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ a) a f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ a) a f₂ rfl q) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd iW g)
        (pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (iW ≫ a) a iW rfl g) (hv' := rfl) (p + q)
        (bivariantRestriction C (gysinSystemOfInvertible C) (iW ≫ a) a iW rfl g (p + q)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (supportedIntersectionMul C a f₁ f₂ sq iW hW c₁ c₂)) =
      supportedIntersectionMul C (g ≫ a) (pullback.snd f₁ g) (pullback.snd f₂ g)
        (isPullback_pullbackMap_of_isPullback f₁ f₂ sq iW hW g) (pullback.snd iW g) (by simp)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f₁ g)
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ a) a f₁ rfl g).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ a) a f₁ rfl g) (hv' := rfl) p
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ a) a f₁ rfl g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁))
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f₂ g)
          (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ a) a f₂ rfl g).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ a) a f₂ rfl g) (hv' := rfl) q
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₂ ≫ a) a f₂ rfl g q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₂)) :=
  bivariantRestriction_supportedIntersectionMul C a f₁ f₂ sq iW hW g
    (isPullback_pullbackMap_of_isPullback f₁ f₂ sq iW hW g) (by simp) (by simp) (by simp) c₁ c₂

/-- **Reduction of the formula for `P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` to an envelope.** Let
`g : Y ⟶ X` be an envelope on which `Lg^*F₁`, `Lg^*F₂` and `Lg^*(F₁ ⊗^L F₂)` are represented by
locally bounded complexes of finite locally free modules. If on `Y` the class of Stacks 0FB2 of
the pullback of `F₁ ⊗^L F₂` is `∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Lg^*F₁) P_{p₂}(Lg^*F₂)`, then
`P_p(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(Z₁ ⟶ X, F₁) P_{p₂}(Z₂ ⟶ X, F₂)` for
the classes of Remark 0GUK. -/
theorem localizedPowerSum_derivedTensor_of_isEnvelope
    (hE₁ : HasDefinedChernClasses F₁) (hE₂ : HasDefinedChernClasses F₂)
    (hE : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂))
    (hg : IsEnvelope g)
    (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₁))
    (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₂))
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)))
    (p : ℕ)
    (hY : (((LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0).pullback
          g).toSituation hc).localizedPowerSum
          (LocalizedChernData.IsZeroOnComplement.pullback
            (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂)) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₁ g) (pullback.snd i₂ g)
            (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
              (pullback.snd i₁ i₂ ≫ i₂) rfl g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).pullback g).toSituation
              hc₁).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₁) q.1.1)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).pullback g).toSituation
              hc₂).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₂) q.1.2))) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0).localizedPowerSum hE
        (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ q.1.1)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ q.1.2)) := by
  refine eq_of_congrBase_restrictionAddHom_eq C a g _ hg ?_
  rw [bivariantRestrictionAddHom_apply,
    LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
    (D := LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 0) hE g hg hc
    (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) p, hY, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [bivariantRestrictionAddHom_apply, bivariantRestriction_bivariantClassDegreeCongr,
    bivariantClassCongrBase_bivariantClassDegreeCongr,
    congrBase_restriction_supportedIntersectionMul C a g i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _
      rfl,
    LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
      (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) hE₁ g hg hc₁ h₁ q.1.1,
    LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
      (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) hE₂ g hg hc₂ h₂ q.1.2]

/-- For `F` zero away from `Z`, the data in degree `p ≥ 1` satisfy the second alternative of
condition (2) of Situation 0GUJ: the zero module is finite locally free of rank `< p`. -/
theorem LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (F : DerivedCategory X.Modules)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F)
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
        i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj F))
    {p : ℕ} (hp : 0 < p) :
    (LocalizedChernData.ofIsZero C a i F hF h p).IsFiniteLocallyFreeOfRankLTOnComplement :=
  exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _) h hp

/-- **Reduction of the formula for `c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` to an envelope**, as
`Stacks.Chow.localizedPowerSum_derivedTensor_of_isEnvelope`: if on `Y` the class of Stacks 0FB2 is
`r₁ c_1(Lg^*F₂) + r₂ c_1(Lg^*F₁)` with `r_i = P_0(Lg^*F_i)`, then
`c_1(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ c_1(Z₂ ⟶ X, F₂) + r₂ c_1(Z₁ ⟶ X, F₁)` for the classes of
Remark 0GUK, with `r_i = P_0(Z_i ⟶ X, F_i)`. -/
theorem localizedChern_one_derivedTensor_of_isEnvelope
    (hE₁ : HasDefinedChernClasses F₁) (hE₂ : HasDefinedChernClasses F₂)
    (hE : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂))
    (hg : IsEnvelope g)
    (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₁))
    (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₂))
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)))
    (hY : (((LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 1).pullback
          g).toSituation hc).localizedChern
          (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
            (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
              (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) one_pos)) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₁ g) (pullback.snd i₂ g)
            (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
              (pullback.snd i₁ i₂ ≫ i₂) rfl g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).pullback g).toSituation
              hc₁).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₁) 0)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₂ g) (pullback.snd i₁ g)
            (isPullback_pullbackMap_of_isPullback i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip
              (pullback.snd i₁ i₂ ≫ i₂) pullback.condition g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).pullback g).toSituation
              hc₂).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₂) 0)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  one_pos))))) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 1).localizedChern hE
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) one_pos) =
      bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0)
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))) := by
  refine eq_of_congrBase_restrictionAddHom_eq C a g _ hg ?_
  rw [bivariantRestrictionAddHom_apply,
    LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
      (D := LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 1) hE g hg hc, hY]
  simp only [map_add, bivariantRestrictionAddHom_apply,
    bivariantRestriction_bivariantClassDegreeCongr,
    bivariantClassCongrBase_bivariantClassDegreeCongr]
  congr 1
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
      _ rfl,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) hE₁ g hg hc₁ h₁ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1) hE₂ g hg hc₂]
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₂ i₁
      (IsPullback.of_hasPullback i₁ i₂).flip _ pullback.condition,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) hE₂ g hg hc₂ h₂ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1) hE₁ g hg hc₁]

/-- **Reduction of the formula for `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂)` to an envelope**, as
`Stacks.Chow.localizedPowerSum_derivedTensor_of_isEnvelope`. Write `r_i = P_0(Z_i ⟶ X, F_i)`,
`γ_{i,p} = c_p(Z_i ⟶ X, F_i)` for the classes of Remark 0GUK and `C(r_i, 2)` for the classes
`Stacks.Chow.LocalizedChernData.rankChoose`. If on `Y` the class of Stacks 0FB2 of the pullback of
`F₁ ⊗^L F₂` is given by the formula of Lemma 0FBF in the corresponding classes of `Lg^*F₁` and
`Lg^*F₂`, then

  `c_2(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = r₁ γ_{2,2} + r₂ γ_{1,2} + C(r₁, 2) γ_{2,1}² +
    ((r₁ r₂) (γ_{2,1} γ_{1,1}) - γ_{2,1} γ_{1,1}) + C(r₂, 2) γ_{1,1}²`

in `A^2(Z₁ ∩ Z₂ ⟶ X)`, with the products of `Stacks.Chow.supportedIntersectionMul` and
`Stacks.Chow.supportedMul`, each summand read in degree `2`. -/
theorem localizedChern_two_derivedTensor_of_isEnvelope
    (hE₁ : HasDefinedChernClasses F₁) (hE₂ : HasDefinedChernClasses F₂)
    (hE : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂))
    (hg : IsEnvelope g)
    (hc₁ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₁))
    (hc₂ : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj F₂))
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (derivedPullback g.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)))
    (hY : (((LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 2).pullback
          g).toSituation hc).localizedChern
          (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
            (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
              (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) two_pos)) =
      ((bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₁ g) (pullback.snd i₂ g)
            (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
              (pullback.snd i₁ i₂ ≫ i₂) rfl g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).pullback g).toSituation
              hc₁).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₁) 0)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 2).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  two_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₂ g) (pullback.snd i₁ g)
            (isPullback_pullbackMap_of_isPullback i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip
              (pullback.snd i₁ i₂ ≫ i₂) pullback.condition g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).pullback g).toSituation
              hc₂).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₂) 0)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 2).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  two_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₁ g) (pullback.snd i₂ g)
            (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
              (pullback.snd i₁ i₂ ≫ i₂) rfl g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            (((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).pullback g).rankChoose
              (LocalizedChernData.IsZeroOnComplement.pullback h₁) 2 two_pos)
            (supportedMul C (pullback.snd i₂ g ≫ (g ≫ a)) (g ≫ a) (pullback.snd i₂ g) rfl
              ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  one_pos)))
              ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  one_pos))))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g ≫ (g ≫ a)) (g ≫ a)
              (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) rfl
              (supportedIntersectionMul C (g ≫ a) (pullback.snd i₁ g) (pullback.snd i₂ g)
            (isPullback_pullbackMap_of_isPullback i₁ i₂ (IsPullback.of_hasPullback i₁ i₂)
              (pullback.snd i₁ i₂ ≫ i₂) rfl g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).pullback g).toSituation
              hc₁).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₁) 0)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).pullback g).toSituation
              hc₂).localizedPowerSum (LocalizedChernData.IsZeroOnComplement.pullback h₂) 0))
              (supportedIntersectionMul C (g ≫ a) (pullback.snd i₂ g) (pullback.snd i₁ g)
            (isPullback_pullbackMap_of_isPullback i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip
              (pullback.snd i₁ i₂ ≫ i₂) pullback.condition g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  one_pos)))
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  one_pos))))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C (g ≫ a) (pullback.snd i₂ g) (pullback.snd i₁ g)
            (isPullback_pullbackMap_of_isPullback i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip
              (pullback.snd i₁ i₂ ≫ i₂) pullback.condition g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            ((((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).pullback g).toSituation
              hc₂).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                  one_pos)))
            ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  one_pos))))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C (g ≫ a) (pullback.snd i₂ g) (pullback.snd i₁ g)
            (isPullback_pullbackMap_of_isPullback i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip
              (pullback.snd i₁ i₂ ≫ i₂) pullback.condition g)
            (pullback.snd (pullback.snd i₁ i₂ ≫ i₂) g) (by simp)
            (((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).pullback g).rankChoose
              (LocalizedChernData.IsZeroOnComplement.pullback h₂) 2 two_pos)
            (supportedMul C (pullback.snd i₁ g ≫ (g ≫ a)) (g ≫ a) (pullback.snd i₁ g) rfl
              ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  one_pos)))
              ((((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).pullback g).toSituation
              hc₁).localizedChern
                (LocalizedChernData.IsFiniteLocallyFreeOfRankLTOnComplement.pullback
                (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                  one_pos)))))))) :
    (LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 2).localizedChern hE
        (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _
          (isZero_derivedTensor_compl_pullback i₁ i₂ hF₁ hF₂ h₁ h₂) two_pos) =
      ((bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 2).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0)
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 2).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                two_pos))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).rankChoose h₁ 2 two_pos)
            (supportedMul C (i₂ ≫ a) a i₂ rfl
              ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
              ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos)))) +
        (bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedMul C ((pullback.snd i₁ i₂ ≫ i₂) ≫ a) a (pullback.snd i₁ i₂ ≫ i₂) rfl
              (supportedIntersectionMul C a i₁ i₂ (IsPullback.of_hasPullback i₁ i₂) _ rfl
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0).localizedPowerSum hE₁ h₁ 0)
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).localizedPowerSum hE₂ h₂ 0))
              (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) -
          bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
            (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1).localizedChern hE₂
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₂
                one_pos))
            ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))) +
        bivariantClassDegreeCongr C _ _ _ _ rfl (by norm_num)
          (supportedIntersectionMul C a i₂ i₁ (IsPullback.of_hasPullback i₁ i₂).flip _
            pullback.condition
            ((LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0).rankChoose h₂ 2 two_pos)
            (supportedMul C (i₁ ≫ a) a i₁ rfl
              ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos))
              ((LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1).localizedChern hE₁
              (LocalizedChernData.isFiniteLocallyFreeOfRankLTOnComplement_ofIsZero C a _ _ _ h₁
                one_pos)))))) := by
  refine eq_of_congrBase_restrictionAddHom_eq C a g _ hg ?_
  rw [bivariantRestrictionAddHom_apply,
    LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
      (D := LocalizedChernData.derivedTensorOfIsZero C a i₁ i₂ hF₁ hF₂ h₁ h₂ 2) hE g hg hc, hY]
  simp only [map_add, map_sub, bivariantRestrictionAddHom_apply,
    bivariantRestriction_bivariantClassDegreeCongr,
    bivariantClassCongrBase_bivariantClassDegreeCongr]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_)
    (congrArg₂ (· - ·) ?_ ?_)) ?_
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₁ i₂
        (IsPullback.of_hasPullback i₁ i₂) _ rfl,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) hE₁ g hg hc₁ h₁ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 2) hE₂ g hg hc₂]
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₂ i₁
        (IsPullback.of_hasPullback i₁ i₂).flip _ pullback.condition,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) hE₂ g hg hc₂ h₂ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 2) hE₁ g hg hc₁]
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₁ i₂
        (IsPullback.of_hasPullback i₁ i₂) _ rfl,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_rankChoose
        (LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) h₁ g 2 two_pos,
      bivariantRestriction_supportedMul, bivariantClassCongrBase_supportedMul,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1) hE₂ g hg hc₂]
  · rw [bivariantRestriction_supportedMul, bivariantClassCongrBase_supportedMul,
      congrBase_restriction_supportedIntersectionMul C a g i₁ i₂
        (IsPullback.of_hasPullback i₁ i₂) _ rfl,
      congrBase_restriction_supportedIntersectionMul C a g i₂ i₁
        (IsPullback.of_hasPullback i₁ i₂).flip _ pullback.condition,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 0) hE₁ g hg hc₁ h₁ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedPowerSum
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) hE₂ g hg hc₂ h₂ 0,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1) hE₂ g hg hc₂,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1) hE₁ g hg hc₁]
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₂ i₁
        (IsPullback.of_hasPullback i₁ i₂).flip _ pullback.condition,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 1) hE₂ g hg hc₂,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1) hE₁ g hg hc₁]
  · rw [congrBase_restriction_supportedIntersectionMul C a g i₂ i₁
        (IsPullback.of_hasPullback i₁ i₂).flip _ pullback.condition,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_rankChoose
        (LocalizedChernData.ofIsZero C a i₂ F₂ hF₂ h₂ 0) h₂ g 2 two_pos,
      bivariantRestriction_supportedMul, bivariantClassCongrBase_supportedMul,
      LocalizedChernData.bivariantClassCongrBase_bivariantRestriction_localizedChern
        (D := LocalizedChernData.ofIsZero C a i₁ F₁ hF₁ h₁ 1) hE₁ g hg hc₁]

end Tensor

end Stacks.Chow
