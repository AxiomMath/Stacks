module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.InfinityClassCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical
public import StacksCore.Tactic.StacksAttribute

/-!
# The class at infinity and the localized Chern classes (Stacks 0FAV)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `Z ⊆ X` be a
closed subscheme, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `Q ∈ D(𝒪_W)` be
a perfect object whose Chern classes are defined, and let `T ⊆ W_∞` be a closed subscheme
containing all points of `W_∞` over `X \ Z` such that `Q|_T` is isomorphic to a finite locally free
module of rank `< p` in degree `0`. With `E = W_∞ ×_X Z` the inverse image of `Z`, Stacks 0F9K
defines

  `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C ∈ A^p(Z ⟶ X)`,

where `C ∈ A⁰(W_∞ ⟶ X)` is the class of Stacks 0F9J and `c'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` is the class
of Stacks 0F9H for the cover `W_∞ = T ∪ E`. **Stacks 0FAV** asserts

  `C ∘ c_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{W_∞}) ∘ C`.

## The argument

On a test scheme `T' ⟶ X` and for `α ∈ A_k(T')` the class `(Z ⟶ X)_* ∘ c'_p(Q)` caps to the
pushforward to `T'` of `c'_p(Q|_E) ∩ C ∩ α`, which by Stacks 0F9I
(`Stacks.Chow.chowPush_closedCoverLocalizedClass_cap`) is `(W_∞ ⟶ X)_*(c_p(Q|_{W_∞}) ∩ C ∩ α)`.
With a lift `β` of `α`, `C ∩ α = i_∞^* β` and `c_p(Q|_{W_∞}) ∩ i_∞^* β = i_∞^*(c_p(Q) ∩ β)`, and
`(W_∞ ⟶ X)_* i_∞^*(c_p(Q) ∩ β) = c_p(Q|_{X × {0}}) ∩ α`
(`Stacks.Chow.GysinAtInfinity.properChowPushforward_infinityGysin_idRule`). This is the
identity `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})` of Stacks 0F9K, from which the first equality
follows. The outer equality `C ∘ c_p(Q|_{X × {0}}) = c_p(Q|_{W_∞}) ∘ C` is
`Stacks.Chow.GysinAtInfinity.commutesWithChowCohomologyClass_gysinAtInfinityClass` at
`x = c_p(Q)`, whose proof is the chain of the source (Stacks 0F9J, bivariance of `c_p(Q)`,
Stacks 0FAR); together they give the second equality.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity` — the class
  `c'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K.

## Main results

* `Stacks.Chow.GysinAtInfinity.properPushforward_localizedChernClassAtInfinity` —
  `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})`, the identity of Stacks 0F9K.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinity_comp_localizedChernClassAtInfinity` —
  **Stacks 0FAV**, both equalities of the display.

## Implementation notes

`Q|_{W_∞}`, `Q|_{X × {0}}` are the derived pullbacks of `Q` along the inclusion of the fibre at
infinity and the section at zero; `Q|_E` and `Q|_T` are the derived pullbacks of `Q|_{W_∞}` along
the inclusions of `E` and `T` into `W_∞`. The class `c'_p(Q|_E)` is
`Stacks.Chow.closedCoverLocalizedClass` of `c_p(Q|_E)`, which is how
`Stacks.Chow.localizedChernClassOfClosedCover` constructs the class of Stacks 0F9H; the
restriction of `c_p(Q|_E)` to `T ∩ E` vanishes because it is the restriction of
`c_p(Q|_T) = 0` (rank `< p`). Bivariant classes are taken at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`; the composites with Chow cohomology classes are read at the
morphism `W_∞ ⟶ X` itself by `Stacks.Chow.bivariantCompositeIdRightHom` and
`Stacks.Chow.bivariantCompositeIdLeftHom`, in degree `0 + p`.

## References

* [Stacks Project, Tag 0FAV](https://stacks.math.columbia.edu/tag/0FAV)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Bookkeeping -/

section Bookkeeping

variable (C : ChowSituation.{u}) (G : GysinSystem C)

/-- Pushing the cap of a class to the test scheme does not see the presentation of its morphism
by an equal one. -/
theorem chowPush_snd_bivariantClassCongr {Y X T : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {f f' : Y ⟶ X}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [IsProper f] [IsProper f'] (hff : f = f')
    (hf : f ≫ sX = sY) (hf' : f' ≫ sX = sY) (n : ℤ) (a : BivariantClass C G sY sX f hf n)
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPush C (pullback.fst f' t ≫ sY) (t ≫ sX) (pullback.snd f' t)
        (pullbackSnd_comp_structureMorphism_eq C sY sX f' hf' t) (k - n)
        ((bivariantClassCongr C G sY sX hff hf hf' n a).cap t k α) =
      chowPush C (pullback.fst f t ≫ sY) (t ≫ sX) (pullback.snd f t)
        (pullbackSnd_comp_structureMorphism_eq C sY sX f hf t) (k - n) (a.cap t k α) := by
  subst hff
  rfl

/-- Pushing the cap of a class along two successive base changes does not see the presentation of
its morphism by an equal one. -/
private theorem chowPush_snd_chowPush_baseChange_bivariantClassCongr {Y' Y X T : Scheme.{u}}
    {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY'] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] (h : Y' ⟶ Y) [IsProper h] (g : Y ⟶ X) [IsProper g]
    {f : Y' ⟶ X} [IsProper f] (hff : f = h ≫ g) (hh : h ≫ sY = sY') (hg : g ≫ sX = sY)
    (hf : f ≫ sX = sY') (hf' : (h ≫ g) ≫ sX = sY') (n : ℤ) (a : BivariantClass C G sY' sX f hf n)
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPush C (pullback.fst g t ≫ sY) (t ≫ sX) (pullback.snd g t)
        (pullbackSnd_comp_structureMorphism_eq C sY sX g hg t) (k - n)
        (chowPush C (pullback.fst (h ≫ g) t ≫ sY') (pullback.fst g t ≫ sY)
          (bivariantPushforwardBaseChange h g t)
          (bivariantPushforwardBaseChange_comp_structure hh g t) (k - n)
          ((bivariantClassCongr C G sY' sX hff hf hf' n a).cap t k α)) =
      chowPush C (pullback.fst f t ≫ sY') (t ≫ sX) (pullback.snd f t)
        (pullbackSnd_comp_structureMorphism_eq C sY' sX f hf t) (k - n) (a.cap t k α) := by
  rw [chowPush_comp C _ _ _ _ _ _ (bivariantPushforwardBaseChange_snd h g t) _ _
    (pullbackSnd_comp_structureMorphism_eq C sY' sX (h ≫ g) hf' t),
    chowPush_snd_bivariantClassCongr C G sY' sX hff hf hf']

/-- A total class whose component of degree `p` vanishes restricts to one whose component of
degree `p` vanishes. -/
theorem TotalChowClass.res_apply_eq_zero {X Y : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) (c : TotalChowClass C sX) (p : ℕ)
    (hc : c p = 0) : TotalChowClass.res h hs c p = 0 := by
  subst hs
  rw [TotalChowClass.res_rfl_apply, hc, map_zero]

/-- The Chern classes of a derived pullback are defined when those of the object are. -/
theorem hasDefinedChernClasses_derivedPullback {X Y : Scheme.{u}} (h : Y ⟶ X)
    {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) :
    HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E) :=
  hasDefinedChernClasses_of_derivedPullback h _ E hE (Iso.refl _)

/-- The Chern class of a derived pullback operates as the Chern class of the object does, on the
composite test morphism. -/
theorem idRule_perfectChernClass_derivedPullback_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (h : Y ⟶ X)
    [LocallyOfFiniteType h] (hs : h ≫ sX = sY) {E : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E))
    (p : ℕ) {V : Scheme.{u}} (v : V ⟶ Y) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ sY) k) (α' : chowGroup C ((v ≫ h) ≫ sX) k) (hα : α ≍ α') :
    (perfectChernClass C sY hE' p).idRule C sY (gysinSystemOfInvertible C) v k α ≍
      (perfectChernClass C sX hE p).idRule C sX (gysinSystemOfInvertible C) (v ≫ h) k α' :=
  idRule_heq_of_res_eq C sX h hs (res_perfectChernClass_derivedPullback_of_eq C sX h hs hE hE') p
    v k α α' hα

end Bookkeeping

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

/-! ### The geometry of Stacks 0F9K -/

section Geometry

variable {X W Z V S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)
  (jZ : Z ⟶ X) (iV : V ⟶ modificationFibreAtInfinity f b)

/-- The restriction `Q|_{W_∞}` of `Q` to the fibre at infinity. -/
abbrev restrictionAtInfinity (Q : DerivedCategory W.Modules) :
    DerivedCategory (modificationFibreAtInfinity f b).Modules :=
  (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q

/-- The Chern classes of `Q|_{W_∞}` are defined when those of `Q` are. -/
theorem hasDefinedChernClasses_restrictionAtInfinity {Q : DerivedCategory W.Modules}
    (hQ : HasDefinedChernClasses Q) : HasDefinedChernClasses (restrictionAtInfinity f b Q) :=
  hasDefinedChernClasses_derivedPullback _ hQ

/-- The inclusion `E = W_∞ ×_X Z ⟶ W_∞` of the inverse image of `Z`. -/
abbrev preimageInclusion : pullback (modificationProjectionAtInfinity f b) jZ ⟶
    modificationFibreAtInfinity f b :=
  pullback.fst (modificationProjectionAtInfinity f b) jZ

/-- The morphism `E ⟶ Z` induced by `b`. -/
abbrev preimageProjection : pullback (modificationProjectionAtInfinity f b) jZ ⟶ Z :=
  pullback.snd (modificationProjectionAtInfinity f b) jZ

/-- `W_∞ = T ∪ E` set theoretically, when `T` contains every point of `W_∞` over `X \ Z`. -/
theorem range_union_range_preimageInclusion
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base) :
    Set.range iV.base ∪ Set.range (preimageInclusion f b jZ).base = Set.univ := by
  refine Set.eq_univ_of_forall fun w ↦ ?_
  by_cases hw : (modificationProjectionAtInfinity f b).base w ∈ Set.range jZ.base
  · right
    rw [Scheme.Pullback.range_fst]
    exact hw
  · exact Or.inl (hV w hw)

/-- The finite-locally-free hypothesis of Stacks 0F9K on `T`: `Q|_T` is isomorphic to a finite
locally free `𝒪_T`-module of rank `< p` sitting in cohomological degree `0`. -/
def RestrictionIsLocallyFreeOfRankLT (Q : DerivedCategory W.Modules) (p : ℕ) : Prop :=
  ∃ M : V.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q) ≅
      (DerivedCategory.singleFunctor V.Modules 0).obj M)

end Geometry

/-! ### The localized Chern class of Stacks 0F9K -/

section Construction

variable (C : ChowSituation.{u}) {X W Z V : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (jZ : Z ⟶ X) [IsClosedImmersion jZ]
  (iV : V ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iV]
  {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

/-- The Chern class `c_p(Q|_{W_∞}) ∈ A^p(W_∞)`. -/
abbrev chernClassAtInfinity :
    chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f) (p : ℤ) :=
  perfectChernClass C (modificationProjectionAtInfinity f b ≫ f)
    (hasDefinedChernClasses_restrictionAtInfinity f b hQ) p

/-- The Chern class `c_p(Q|_E) ∈ A^p(E)`. -/
abbrev chernClassOnPreimage :
    chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) (p : ℤ) :=
  perfectChernClass C (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
    (hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ)) p

/-- The restriction of `c_p(Q|_{W_∞})` to `E` is `c_p(Q|_E)`. -/
theorem chowCohomologyRestriction_chernClassAtInfinity_preimage :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chernClassAtInfinity C f b hQ p) =
      chernClassOnPreimage C f b jZ hQ p := by
  rw [← TotalChowClass.res_rfl_apply, res_perfectChernClass_derivedPullback C _ _ _
    (hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ))]

/-- `c_p(Q|_T) = 0` when `Q|_T` is finite locally free of rank `< p`. -/
theorem chowCohomologyRestriction_chernClassAtInfinity_eq_zero
    (hres : ∃ M : V.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q) ≅
        (DerivedCategory.singleFunctor V.Modules 0).obj M)) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) iV (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chernClassAtInfinity C f b hQ p) = 0 := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hres
  rw [← TotalChowClass.res_rfl_apply, res_perfectChernClass_derivedPullback C _ iV _
    (hasDefinedChernClasses_derivedPullback iV
      (hasDefinedChernClasses_restrictionAtInfinity f b hQ))]
  exact perfectChernClass_apply_eq_zero_of_iso_single C _ _ M hM e

variable {f b iV p} in
/-- The restriction of `c_p(Q|_E)` to `T ∩ E` vanishes: it is the restriction of
`c_p(Q|_T) = 0`. -/
theorem chowCohomologyRestriction_chernClassOnPreimage_eq_zero
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
        (pullback.snd iV (preimageInclusion f b jZ)) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chernClassOnPreimage C f b jZ hQ p) = 0 := by
  have h0 := chowCohomologyRestriction_chernClassAtInfinity_eq_zero C f b iV hQ p hres
  rw [← TotalChowClass.res_rfl_apply] at h0
  have key : TotalChowClass.res (pullback.snd iV (preimageInclusion f b jZ)) rfl
      (TotalChowClass.res (preimageInclusion f b jZ) rfl
        (perfectChernClass C (modificationProjectionAtInfinity f b ≫ f)
          (hasDefinedChernClasses_restrictionAtInfinity f b hQ))) =
      TotalChowClass.res (pullback.fst iV (preimageInclusion f b jZ))
        (by rw [← Category.assoc, pullback.condition, Category.assoc])
        (TotalChowClass.res iV rfl
          (perfectChernClass C (modificationProjectionAtInfinity f b ≫ f)
            (hasDefinedChernClasses_restrictionAtInfinity f b hQ))) := by
    rw [TotalChowClass.res_res, TotalChowClass.res_res]
    exact TotalChowClass.res_congr pullback.condition.symm _ _ _
  rw [← chowCohomologyRestriction_chernClassAtInfinity_preimage, ← TotalChowClass.res_rfl_apply,
    ← TotalChowClass.res_rfl_apply, key]
  exact TotalChowClass.res_apply_eq_zero C _ _ _ _ h0

variable {f b iV p} in
/-- **The class `c'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` of Stacks 0F9H** for the cover `W_∞ = T ∪ E`: the
localized class of `c_p(Q|_E)`, which on a test scheme sends `i'_{T,*} α_T + i'_{E,*} α_E` to
`c_p(Q|_E) ∩ α_E`. -/
def localizedChernClassOnPreimage
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) rfl (p : ℤ) :=
  closedCoverLocalizedClass C (modificationProjectionAtInfinity f b ≫ f)
    (iV ≫ modificationProjectionAtInfinity f b ≫ f)
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) iV rfl
    (preimageInclusion f b jZ) rfl (range_union_range_preimageInclusion f b jZ iV hV)
    (chernClassOnPreimage C f b jZ hQ p)
    (chowCohomologyRestriction_chernClassOnPreimage_eq_zero C jZ hQ hres)

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion jZ] in
/-- The composites `E ⟶ Z ⟶ X ⟶ S` and `E ⟶ W_∞ ⟶ X ⟶ S` agree. -/
theorem preimageProjection_comp :
    preimageProjection f b jZ ≫ jZ ≫ f =
      preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc]

variable {f b iV p} in
/-- **The class `c'_p(Q) ∈ A^p(Z ⟶ X)` of Stacks 0F9K**:
`c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`, with `E = W_∞ ×_X Z`, `C ∈ A⁰(W_∞ ⟶ X)` the class of
Stacks 0F9J and `c'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` the class of Stacks 0F9H; the composite is a class for
`E ⟶ W_∞ ⟶ X = E ⟶ Z ⟶ X` of degree `p + 0 = p`, pushed forward along the proper `E ⟶ Z` by
Stacks 0EPK. -/
def localizedChernClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    BivariantClass C (gysinSystemOfInvertible C) (jZ ≫ f) f jZ rfl (p : ℤ) :=
  canonicalBivariantProperPushforward C
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) (jZ ≫ f) f
    (preimageProjection f b jZ) jZ (preimageProjection_comp C f b jZ) rfl (p : ℤ)
    (bivariantClassCongr C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
      pullback.condition
      (comp_comp_structureMorphism_eq rfl rfl)
      (comp_comp_structureMorphism_eq (preimageProjection_comp C f b jZ) rfl) (p : ℤ)
      (bivariantClassCongrDeg C (gysinSystemOfInvertible C)
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b)
        (comp_comp_structureMorphism_eq rfl rfl) (add_zero (p : ℤ))
        (bivariantCompositeOfInvertible C
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
          (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b jZ)
          (modificationProjectionAtInfinity f b) rfl rfl (p : ℤ) 0
          (localizedChernClassOnPreimage C jZ hQ hV hres) (gysinAtInfinityClass C f b hA))))

variable {f b iV p} in
/-- The class `(Z ⟶ X)_* ∘ c'_p(Q) ∈ A^p(X)`: the pushforward of `c'_p(Q)` along the closed
immersion `Z ⟶ X` by Stacks 0EPK, a class for the identity of `X`. -/
def properPushforwardLocalizedChernClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) f (p : ℤ) :=
  canonicalBivariantProperPushforward C (jZ ≫ f) f f jZ (𝟙 X) rfl (Category.id_comp f) (p : ℤ)
    (bivariantClassCongr C (gysinSystemOfInvertible C) (jZ ≫ f) f (Category.comp_id jZ).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp f)) (p : ℤ)
      (localizedChernClassAtInfinity C hA jZ hQ hV hres))

/-- The Chern class `c_p(Q|_{X × {0}}) ∈ A^p(X)` of the restriction of `Q` along the section at
zero `i_0 : X ⟶ W`. -/
abbrev chernClassAtZero :
    chowCohomologyComponent C (gysinSystemOfInvertible C) f (p : ℤ) :=
  haveI := hA
  perfectChernClass C f (hasDefinedChernClasses_derivedPullback
    (modificationSectionAtZero f b inferInstance) hQ) p

/-- The Chern class `c_p(Q) ∈ A^p(W)`. -/
abbrev chernClassOnModification :
    chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f)
      (p : ℤ) :=
  perfectChernClass C (modificationProjection f b ≫ f) hQ p

/-- On a test scheme over `X`, `c_p(Q|_{X × {0}})` operates as `c_p(Q)` does on the composite
with the section at zero `i_0 : X ⟶ W`. -/
theorem idRule_chernClassAtZero_heq {V' : Scheme.{u}} (v : V' ⟶ X) [LocallyOfFiniteType v]
    (k : ℤ) (α : chowGroup C (v ≫ f) k)
    (α' : chowGroup C ((v ≫ modificationSectionAtZero f b (haveI := hA; inferInstance)) ≫
      (modificationProjection f b ≫ f)) k) (hα : α ≍ α') :
    (chernClassAtZero C f b hA hQ p).idRule C f (gysinSystemOfInvertible C) v k α ≍
      (chernClassOnModification C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ modificationSectionAtZero f b (haveI := hA; inferInstance)) k α' := by
  have := hA
  exact idRule_perfectChernClass_derivedPullback_heq C (modificationProjection f b ≫ f) f
    (modificationSectionAtZero f b inferInstance)
    (by rw [← Category.assoc, modificationSectionAtZero_comp, Category.id_comp]) hQ _ p v k α α'
    hα

/-- On a test scheme over `W_∞`, `c_p(Q|_{W_∞})` operates as `c_p(Q)` does on the composite with
the inclusion `W_∞ ⟶ W`. -/
theorem idRule_chernClassAtInfinity_heq {V' : Scheme.{u}}
    (v : V' ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ (modificationProjectionAtInfinity f b ≫ f)) k)
    (α' : chowGroup C ((v ≫ modificationInclusionAtInfinity f b) ≫
      (modificationProjection f b ≫ f)) k) (hα : α ≍ α') :
    (chernClassAtInfinity C f b hQ p).idRule C _ (gysinSystemOfInvertible C) v k α ≍
      (chernClassOnModification C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ modificationInclusionAtInfinity f b) k α' :=
  idRule_perfectChernClass_derivedPullback_heq C (modificationProjection f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) (modificationInclusionAtInfinity f b)
    (Category.assoc _ _ _).symm hQ _ p v k α α' hα

variable {f b iV p} in
/-- **The identity of Stacks 0F9K**: `(Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{X × {0}})` in `A^p(X)`. -/
theorem properPushforward_localizedChernClassAtInfinity
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    properPushforwardLocalizedChernClassAtInfinity C hA jZ hQ hV hres =
      chernClassAtZero C f b hA hQ p := by
  have := hA
  refine BivariantClass.eq_of_idRule_eq C f (gysinSystemOfInvertible C) _ _ fun g _ k α ↦ ?_
  set a := localizedChernClassOnPreimage C jZ hQ hV hres
  set comp := bivariantCompositeOfInvertible C
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
    (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b jZ)
    (modificationProjectionAtInfinity f b) rfl rfl (p : ℤ) 0 a (gysinAtInfinityClass C f b hA)
  set c4 := bivariantClassCongrDeg C (gysinSystemOfInvertible C)
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b)
    (comp_comp_structureMorphism_eq rfl rfl) (add_zero (p : ℤ)) comp
  have e1 : (properPushforwardLocalizedChernClassAtInfinity C hA jZ hQ hV hres).idRule C f
        (gysinSystemOfInvertible C) g k α =
      chowPush C (pullback.fst (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g ≫
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ (comp_comp_structureMorphism_eq rfl rfl) g)
        (k - p) (c4.cap g k α) := by
    rw [BivariantClass.idRule_apply]
    show chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
    rw [chowPush_snd_chowPush_baseChange_bivariantClassCongr C (gysinSystemOfInvertible C) jZ
      (𝟙 X) (Category.comp_id jZ).symm rfl (Category.id_comp f)]
    show chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
    rw [chowPush_snd_chowPush_baseChange_bivariantClassCongr C (gysinSystemOfInvertible C)
      (preimageProjection f b jZ) jZ pullback.condition (preimageProjection_comp C f b jZ) rfl]
  rw [e1]
  set y := (gysinAtInfinityClass C f b hA).cap g k α
  set z := a.cap (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0) y
  have e2 : c4.cap g k α ≍ properChowPushforward C _ _
      (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) g
        (preimageInclusion f b jZ)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ g) (k - 0 - p)
      (properPushforwardDescends C _ _ _ _ _) z := by
    rw [bivariantClassCongrDeg_cap]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    exact chowGroupDegreeEquiv_heq C _ _ _
  have e3 : chowPush C _ (g ≫ f)
        (pullback.snd (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ (comp_comp_structureMorphism_eq rfl rfl) g)
        (k - 0 - p)
        (properChowPushforward C _ _
          (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) g
            (preimageInclusion f b jZ)).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ g) (k - 0 - p)
          (properPushforwardDescends C _ _ _ _ _) z) =
      chowPush C (pullback.fst (modificationProjectionAtInfinity f b) g ≫
          (modificationProjectionAtInfinity f b ≫ f)) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (pullbackSnd_comp_structureMorphism_eq C _ f _ rfl g) (k - 0 - p)
        ((chernClassAtInfinity C f b hQ p).idRule C _ (gysinSystemOfInvertible C)
          (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0) y) := by
    rw [← chowPush_closedCoverLocalizedClass_cap C (modificationProjectionAtInfinity f b ≫ f) iV
      (preimageInclusion f b jZ) (range_union_range_preimageInclusion f b jZ iV hV)
      (chernClassAtInfinity C f b hQ p) (chernClassOnPreimage C f b jZ hQ p)
      (chowCohomologyRestriction_chernClassOnPreimage_eq_zero C jZ hQ hres)
      (chowCohomologyRestriction_chernClassAtInfinity_preimage C f b jZ hQ p)
      (chowCohomologyRestriction_chernClassAtInfinity_eq_zero C f b iV hQ p hres)]
    show chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ z) =
      chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ z)
    rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
    · exact chowPush_congr C _ _ (pullbackRightPullbackFstIso_hom_snd _ _ _) _ _ _ _
    all_goals
      (try rw [pullbackRightPullbackFstIso_hom_snd])
      rw [Category.assoc, ← pullback.condition_assoc, ← pullback.condition_assoc]
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) g k α
  have hy : y ≍ infinityGysin C f b g k β := by
    rw [show y = _ from gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ, infinityGysin_apply]
    exact chowGroupDegreeEquiv_heq C _ _ _
  refine eq_of_heq ((properChowPushforward_heq C _ _ _ _ (by ring : k - p = k - 0 - p) _
    (properPushforwardDescends C _ _ _ _ _) e2).trans ?_)
  refine (heq_of_eq e3).trans ?_
  rw [ ← properChowPushforward_infinityGysin_idRule C f b g
    (chernClassOnModification C f b hQ p) (chernClassAtZero C f b hA hQ p)
    (idRule_chernClassAtZero_heq C f b hA hQ p) hβ]
  refine properChowPushforward_heq C _ _ _ _ (by ring : k - 0 - p = k - p) _
    (properPushforwardDescends C _ _ _ _ _) ?_
  refine (IdentityCapRule.heq_congr C _ ((chernClassAtInfinity C f b hQ p).idRule C _
    (gysinSystemOfInvertible C)) rfl (sub_zero k) hy).trans ?_
  exact idRule_infinityGysin_heq C f b g (chernClassOnModification C f b hQ p)
    (chernClassAtInfinity C f b hQ p) (idRule_chernClassAtInfinity_heq C f b hQ p) k β

end Construction

/-! ### Stacks 0FAV -/

section Statement

variable (C : ChowSituation.{u}) {X W Z V : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]

/-- **Stacks 0FAV.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over
`S`, let `Z ⊆ X` be a closed subscheme, let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an
isomorphism over `𝐀¹_X` (assumption (A1)), and let `Q ∈ D(𝒪_W)` be a perfect object whose Chern
classes are defined (assumption (A0)). Let `T ⊆ W_∞` be a closed subscheme containing all points
of `W_∞` lying over `X \ Z` such that `Q|_T` is isomorphic to a finite locally free
`𝒪_T`-module of rank `< p` sitting in cohomological degree `0` (assumption (A2), in the case of
the lemma). Let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J and `c'_p(Q) ∈ A^p(Z ⟶ X)` the
class of Stacks 0F9K. Then

  `C ∘ c_p(Q|_{X × {0}}) = C ∘ (Z ⟶ X)_* ∘ c'_p(Q) = c_p(Q|_{W_∞}) ∘ C`

in `A^p(W_∞ ⟶ X)`. Here `X × {0}` is identified with `X` by the section at zero, the classes
`c_p` are those of Stacks 0GUD, the composites are those of Stacks 0B75 read at `W_∞ ⟶ X` in
degree `0 + p`, and `(Z ⟶ X)_* ∘ c'_p(Q) ∈ A^p(X)` is the pushforward of Stacks 0EPK. -/
@[stacks 0FAV]
theorem gysinAtInfinity_comp_localizedChernClassAtInfinity
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (jZ : Z ⟶ X) [IsClosedImmersion jZ]
    (iV : V ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iV]
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    {Q : DerivedCategory W.Modules}
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    bivariantCompositeIdRightHom C (gysinSystemOfInvertible C) f
        (modificationProjectionAtInfinity f b)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) (p : ℤ) 0
        (gysinAtInfinityClass C f b hA) (chernClassAtZero C f b hA hQ p) =
      bivariantCompositeIdRightHom C (gysinSystemOfInvertible C) f
        (modificationProjectionAtInfinity f b)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) (p : ℤ) 0
        (gysinAtInfinityClass C f b hA)
        (properPushforwardLocalizedChernClassAtInfinity C hA jZ hQ hV hres) ∧
    bivariantCompositeIdRightHom C (gysinSystemOfInvertible C) f
        (modificationProjectionAtInfinity f b)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) (p : ℤ) 0
        (gysinAtInfinityClass C f b hA)
        (properPushforwardLocalizedChernClassAtInfinity C hA jZ hQ hV hres) =
      bivariantCompositeIdLeftHom C (gysinSystemOfInvertible C) f
        (modificationProjectionAtInfinity f b)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) (p : ℤ) 0
        (gysinAtInfinityClass C f b hA) (chernClassAtInfinity C f b hQ p) := by
  rw [properPushforward_localizedChernClassAtInfinity C hA jZ hQ hV hres]
  exact ⟨rfl, commutesWithChowCohomologyClass_gysinAtInfinityClass C f b hA
    (chernClassOnModification C f b hQ p) (chernClassAtZero C f b hA hQ p)
    (chernClassAtInfinity C f b hQ p) (idRule_chernClassAtZero_heq C f b hA hQ p)
    (idRule_chernClassAtInfinity_heq C f b hQ p)⟩

end Statement

end GysinAtInfinity

end Stacks.Chow

end
