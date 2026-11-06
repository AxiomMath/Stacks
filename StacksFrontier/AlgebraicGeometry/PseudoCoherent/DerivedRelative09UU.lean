module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 09UU, the equivalence of clauses (1) and (2)

Let `i : X ⟶ P` be a closed immersion of schemes and let `p : P ⟶ S` be locally of finite type.
For an object `E` of `D(𝒪_X)` and an integer `m`, this file proves that `E` is relatively
`m`-pseudo-coherent for `i ≫ p` if and only if the unbounded derived pushforward `Ri_*E` is
relatively `m`-pseudo-coherent for `p`.

The argument is local on `P` and on `S`. Relative `m`-pseudo-coherence is, by Stacks 09UJ, the
local condition of Stacks 09UI at *every* compatible pair of affine opens, and the two sides are
compared pair by pair: for an affine open `W` of `P` lying over an affine open `T` of `S`, the
affine open `i ⁻¹ᵁ W` of `X` lies over `T`, and the condition at `(i ⁻¹ᵁ W, T)` for `(i ≫ p, E)`
agrees with the condition at `(W, T)` for `(p, Ri_*E)`.

The comparison at one pair is the restriction square for a pushforward. Picking any closed
immersion `e : W ⟶ 𝔸ᴺ_T` over `T`, the composite `(i ∣_ W) ≫ e` is a closed immersion of
`i ⁻¹ᵁ W` into the same affine space over `T`, and
`(Re_*)((Ri_*E)|_W) ≅ (R((i ∣_ W) ≫ e)_*)(E|_{i ⁻¹ᵁ W})`, so the two pseudo-coherence conditions
are literally the same condition on the same object of `D(𝒪_{𝔸ᴺ_T})`. Stacks 09VC is what lets
`e` be chosen freely on the `P` side while the hypothesis on the `X` side supplies some other
closed immersion.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.derivedRestrictPushforwardIso`: the restriction square for a
  pushforward along a closed immersion, on unbounded derived categories.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_iff`:
  the local condition of Stacks 09UI for `(e, (Ri_*E)|_W)` and for `((i ∣_ W) ≫ e, E|_{i ⁻¹ᵁ W})`
  agree.
* `AlgebraicGeometry.isPseudoCoherentFromOnAffinePair_pushforward_iff`: the pair condition of
  Stacks 09UJ at `(i ⁻¹ᵁ W, T)` for `(i ≫ p, E)` agrees with the one at `(W, T)` for
  `(p, i_*E)`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforwardRelative`:
  **Stacks 09UU, the equivalence of clauses (1) and (2).**

## Implementation notes

**The restriction square.** The module-level square
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`,
`i_* ⋙ (·)|_W ≅ (·)|_{i ⁻¹ᵁ W} ⋙ (i ∣_ W)_*`, is proved for an arbitrary morphism of schemes and
an arbitrary open of the target. All four functors in it are exact when `i` is a closed immersion
— pushforward along a closed immersion is right exact by Stacks 08KS, and restriction along an
open immersion is exact — so the square descends to unbounded derived categories by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, applied to the square on one side and to the
identity isomorphism on the other, exactly as in
`AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardIso`. Nothing is computed on sections,
and no `eqToIso` appears: an `Eq.rec` in a data position of a derived-category isomorphism is a
kernel timeout here. The ringed-space form of the square is not used, because it is stated with
`AlgebraicGeometry.RingedSpace.restrictHom` and
`AlgebraicGeometry.RingedSpace.restrictModules`, and crossing to Mathlib's `morphismRestrict` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` would reintroduce exactly that transport.

**Why the two directions are not symmetric.** The implication from `Ri_*E` to `E` cannot be
proved pair by pair on the `X` side: an affine open of `X` need not be `i ⁻¹ᵁ W` for any affine
open `W` of `P`. It is proved instead against the covers that Stacks 09UI asks for — the affine
opens of `S`, and over each of them the preimages under `i` of the affine opens of `P` contained
in its inverse image, which do cover and are affine because `i ∣_ W` is a closed immersion into
an affine scheme.

**`Ri_*` and `i_*`.** The statement is written with the chosen total right derived functor
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, the same `Ri_*` as in
`AlgebraicGeometry.Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom`, so that the two
clauses of Stacks 09UU compose. Inside the proof it is replaced by
`(AlgebraicGeometry.Scheme.Modules.pushforward i).mapDerivedCategory` along
`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`, which is legitimate
because relative `m`-pseudo-coherence depends only on the isomorphism class of its argument
(`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_iso`).

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.6 (09UU)](https://stacks.math.columbia.edu/tag/09UU)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 17.6.1 (01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Preimages of affine opens under a closed immersion -/

/-- The preimage of an affine open under a closed immersion is an affine open: the restricted
morphism `i ∣_ W : i ⁻¹ᵁ W ⟶ W` is a closed immersion, hence affine, and `W` is affine. -/
public theorem isAffineOpen_preimage_of_isClosedImmersion {X P : Scheme.{u}} (i : X ⟶ P)
    [IsClosedImmersion i] {W : P.Opens} (hW : IsAffineOpen W) : IsAffineOpen (i ⁻¹ᵁ W) :=
  have : IsAffine (W : Scheme.{u}) := hW
  isAffine_of_isAffineHom (i ∣_ W)

/-- If an open `W` of `P` lies over an open `T` of `S` for `p : P ⟶ S`, then `i ⁻¹ᵁ W` lies over
`T` for `i ≫ p`. -/
public theorem preimage_le_comp_preimage {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    {W : P.Opens} {T : S.Opens} (h : W ≤ p ⁻¹ᵁ T) : i ⁻¹ᵁ W ≤ (i ≫ p) ⁻¹ᵁ T := by
  rw [Scheme.Hom.comp_preimage]
  exact fun x hx => h hx

/-- The restriction of `i` over an open `W` of `P`, followed by the restriction of `p` from `W` to
an open `T` of `S` containing its image, is the restriction of `i ≫ p` from `i ⁻¹ᵁ W` to `T`.

Both sides become `(i ⁻¹ᵁ W).ι ≫ i ≫ p` after composing with the inclusion of `T`, which is a
monomorphism. -/
public theorem morphismRestrict_comp_resLE {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    {W : P.Opens} {T : S.Opens} (h : W ≤ p ⁻¹ᵁ T) :
    (i ∣_ W) ≫ p.resLE T W h =
      (i ≫ p).resLE T (i ⁻¹ᵁ W) (preimage_le_comp_preimage i p h) := by
  rw [← cancel_mono T.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
    ← Category.assoc, morphismRestrict_ι, Category.assoc]

namespace Scheme.Modules

/-! ### The restriction square on derived categories -/

/-- **`(i_*E)|_W ≅ (i ∣_ W)_*(E|_{i ⁻¹ᵁ W})` on unbounded derived categories**, for a closed
immersion `i : X ⟶ P` of schemes and an open `W` of `P`.

The module-level square is
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`. Both of its legs are
composites of exact functors — pushforward along a closed immersion is right exact, and
restriction along an open immersion is exact — so each descends to the derived category and is
identified with the derived functor of the composite by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, the left leg along the square itself and the
right leg along the identity isomorphism. -/
public def derivedRestrictPushforwardIso {X P : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i]
    (W : P.Opens) :
    (pushforward i).mapDerivedCategory ⋙ (restrictFunctor W.ι).mapDerivedCategory ≅
      (restrictFunctor (i ⁻¹ᵁ W).ι).mapDerivedCategory ⋙
        (pushforward (i ∣_ W)).mapDerivedCategory := by
  have : PreservesFiniteLimits (restrictFunctor (i ⁻¹ᵁ W).ι ⋙ pushforward (i ∣_ W)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (restrictFunctor (i ⁻¹ᵁ W).ι ⋙ pushforward (i ∣_ W)) :=
    comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIsoOfCompIso
      (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i W) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (restrictFunctor (i ⁻¹ᵁ W).ι ⋙ pushforward (i ∣_ W)))).symm

/-- **The local condition of Stacks 09UI crosses the restriction square.** Let `i : X ⟶ P` be a
closed immersion, let `W` be an open of `P` and let `e : W ⟶ Y` be a closed immersion. Then
`Re_*((i_*E)|_W)` is `m`-pseudo-coherent on `Y` if and only if
`R((i ∣_ W) ≫ e)_*(E|_{i ⁻¹ᵁ W})` is.

Both conditions unfold, by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_comp_iff`, to sheaf-level
`m`-pseudo-coherence of `e_*` applied to the two corners of the derived restriction square
`AlgebraicGeometry.Scheme.Modules.derivedRestrictPushforwardIso`, which are isomorphic. -/
public theorem isPseudoCoherentFromAfterPushforward_morphismRestrict_iff {X P Y : Scheme.{u}}
    (i : X ⟶ P) [IsClosedImmersion i] (W : P.Opens) (e : (W : Scheme.{u}) ⟶ Y)
    [IsClosedImmersion e] (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward e
        ((restrictFunctor W.ι).mapDerivedCategory.obj
          ((pushforward i).mapDerivedCategory.obj E)) m ↔
      IsPseudoCoherentFromAfterPushforward ((i ∣_ W) ≫ e)
        ((restrictFunctor (i ⁻¹ᵁ W).ι).mapDerivedCategory.obj E) m := by
  rw [isPseudoCoherentFromAfterPushforward_iff, isPseudoCoherentFromAfterPushforward_comp_iff]
  exact ⟨fun h => h.of_iso ((pushforward e).mapDerivedCategory.mapIso
      ((derivedRestrictPushforwardIso i W).app E)),
    fun h => h.of_iso ((pushforward e).mapDerivedCategory.mapIso
      ((derivedRestrictPushforwardIso i W).app E).symm)⟩

end Scheme.Modules

/-! ### The comparison at one compatible pair of affine opens -/

/-- **The pair condition of Stacks 09UJ for `(i ≫ p, E)` at `(i ⁻¹ᵁ W, T)` agrees with the one
for `(p, i_*E)` at `(W, T)`.** Here `i : X ⟶ P` is a closed immersion, `p : P ⟶ S` is locally of
finite type, `W` is an affine open of `P` and `T` an affine open of `S` with `W ⊆ p ⁻¹ᵁ T`.

From right to left nothing is needed beyond the restriction square: a closed immersion
`e : W ⟶ 𝔸ᴺ_T` over `T` witnessing the condition at `(W, T)` is turned into the closed immersion
`(i ∣_ W) ≫ e` of `i ⁻¹ᵁ W` into the same affine space over `T`, and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_iff`
carries the condition across.

From left to right the hypothesis supplies some closed immersion of `i ⁻¹ᵁ W` into an affine
space over `T`, which need not factor through `W` at all. Choose any closed immersion
`e : W ⟶ 𝔸ᴺ_T` over `T`, which exists by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`; Stacks 09VC in the form
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin` moves the hypothesis
onto `(i ∣_ W) ≫ e`, and the restriction square carries it back onto `e`. -/
public theorem isPseudoCoherentFromOnAffinePair_pushforward_iff {X P S : Scheme.{u}} (i : X ⟶ P)
    (p : P ⟶ S) [IsClosedImmersion i] [LocallyOfFiniteType p] (E : DerivedCategory X.Modules)
    (m : ℤ) (W : P.affineOpens) (T : S.affineOpens) (hWT : W.1 ≤ p ⁻¹ᵁ T.1) :
    (i ≫ p).IsPseudoCoherentFromOnAffinePair E m
        ⟨i ⁻¹ᵁ W.1, isAffineOpen_preimage_of_isClosedImmersion i W.2⟩ T
        (preimage_le_comp_preimage i p hWT) ↔
      p.IsPseudoCoherentFromOnAffinePair
        ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E) m W T hWT := by
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have hTaff : IsAffine (T.1 : Scheme.{u}) := T.2
  have hVaff : IsAffine ((i ⁻¹ᵁ W.1 : X.Opens) : Scheme.{u}) :=
    isAffineOpen_preimage_of_isClosedImmersion i W.2
  have := locallyOfFiniteType_resLE (i ≫ p) T.1 (i ⁻¹ᵁ W.1)
    (preimage_le_comp_preimage i p hWT)
  constructor
  · intro hL
    obtain ⟨N, e, hce, hoe⟩ := exists_isClosedImmersion_affineSpace_resLE p T W hWT
    refine ⟨N, e, hce, hoe, ?_⟩
    rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_iff i W.1 e E m]
    refine (Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin
      ((i ≫ p).resLE T.1 (i ⁻¹ᵁ W.1) (preimage_le_comp_preimage i p hWT)) _ m).mp hL
      N ((i ∣_ W.1) ≫ e) inferInstance ?_
    rw [Category.assoc, hoe, morphismRestrict_comp_resLE]
  · rintro ⟨N, e, hce, hoe, hpred⟩
    exact ⟨N, (i ∣_ W.1) ≫ e, inferInstance,
      by rw [Category.assoc, hoe, morphismRestrict_comp_resLE],
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_iff i W.1 e E m).mp
        hpred⟩

/-! ### Stacks 09UU, the equivalence of clauses (1) and (2) -/

/-- **Stacks 09UU, the equivalence of clauses (1) and (2), with `i_*` in place of `Ri_*`.** For a
closed immersion `i : X ⟶ P` and `p : P ⟶ S` locally of finite type, `E` is relatively
`m`-pseudo-coherent for `i ≫ p` if and only if `i_*E`, formed with the functor induced on derived
categories by the exact functor `i_*`, is relatively `m`-pseudo-coherent for `p`.

For the forward implication, Stacks 09UJ turns the hypothesis into the pair condition at every
compatible pair of affine opens of `X` over `S`, in particular at `(i ⁻¹ᵁ W, T)` for every
compatible pair `(W, T)` of affine opens of `P` over `S`;
`AlgebraicGeometry.isPseudoCoherentFromOnAffinePair_pushforward_iff` converts each of those into
the pair condition for `(p, i_*E)` at `(W, T)`, and
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair` assembles them.

The converse is not pair-by-pair on `X`, because an affine open of `X` need not be a preimage.
Stacks 09UJ turns the hypothesis into the pair condition at every compatible pair of affine opens
of `P` over `S`, and the covers required by Stacks 09UI are built by hand: the affine opens of
`S`, and over each the preimages under `i` of the affine opens of `P` contained in its inverse
image. Those preimages are affine by
`AlgebraicGeometry.isAffineOpen_preimage_of_isClosedImmersion` and cover
`(i ≫ p) ⁻¹ᵁ T` because the affine opens cover `p ⁻¹ᵁ T`
(`AlgebraicGeometry.iSup_affineOpens_subtype_eq`) and taking preimages commutes with suprema
(`AlgebraicGeometry.Scheme.Hom.preimage_iSup`). -/
@[sga "6 III 2.1" "special case"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_pushforwardMapDerivedCategory
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S) [IsClosedImmersion i] [LocallyOfFiniteType p]
    (E : DerivedCategory X.Modules) (m : ℤ) :
    (i ≫ p).IsPseudoCoherentFrom E m ↔
      p.IsPseudoCoherentFrom ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E) m := by
  refine ⟨fun h => Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair p _ m fun W T hWT =>
    (isPseudoCoherentFromOnAffinePair_pushforward_iff i p E m W T hWT).mp
      (Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom (i ≫ p) h _ T _),
    fun h => ?_⟩
  refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun T => ?_⟩
  refine ⟨{W : P.affineOpens // W.1 ≤ p ⁻¹ᵁ (T : S.Opens)},
    fun W => ⟨i ⁻¹ᵁ W.1.1, isAffineOpen_preimage_of_isClosedImmersion i W.1.2⟩, ?_, fun W => ?_⟩
  · calc (⨆ W : {W : P.affineOpens // W.1 ≤ p ⁻¹ᵁ (T : S.Opens)}, (i ⁻¹ᵁ W.1.1 : X.Opens))
          = i ⁻¹ᵁ
            (⨆ W : {W : P.affineOpens // W.1 ≤ p ⁻¹ᵁ (T : S.Opens)}, (W.1.1 : P.Opens)) :=
          (i.preimage_iSup _).symm
      _ = i ⁻¹ᵁ (p ⁻¹ᵁ (T : S.Opens)) := by rw [iSup_affineOpens_subtype_eq]
      _ = (i ≫ p) ⁻¹ᵁ (T : S.Opens) := (Scheme.Hom.comp_preimage i p _).symm
  · exact ⟨preimage_le_comp_preimage i p W.2,
      (isPseudoCoherentFromOnAffinePair_pushforward_iff i p E m W.1 T W.2).mpr
        (Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom p h W.1 T W.2)⟩

/-- **Stacks 09UU, the equivalence of clauses (1) and (2).** Let `i : X ⟶ P` be a closed immersion
of schemes and let `p : P ⟶ S` be locally of finite type. For an object `E` of `D(𝒪_X)` and an
integer `m`, `E` is relatively `m`-pseudo-coherent for `i ≫ p` if and only if the unbounded
derived pushforward `Ri_*E` is relatively `m`-pseudo-coherent for `p`.

This is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_pushforwardMapDerivedCategory` transported
along `Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`, which identifies
the chosen total right derived functor
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` with the functor the
exact `i_*` induces on derived categories; relative `m`-pseudo-coherence depends only on the
isomorphism class of its argument. -/
@[stacks 09UU "the equivalence of clauses (1) and (2), at a closed immersion",
  sga "6 III 2.1" "special case"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforwardRelative {X P S : Scheme.{u}}
    (i : X ⟶ P) (p : P ⟶ S) [IsClosedImmersion i] [LocallyOfFiniteType p]
    (E : DerivedCategory X.Modules) (m : ℤ) :
    (i ≫ p).IsPseudoCoherentFrom E m ↔
      p.IsPseudoCoherentFrom
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m :=
  (Scheme.Hom.isPseudoCoherentFrom_iff_pushforwardMapDerivedCategory i p E m).trans
    ⟨fun h => Scheme.Hom.IsPseudoCoherentFrom.of_iso p h
        ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E).symm,
      fun h => Scheme.Hom.IsPseudoCoherentFrom.of_iso p h
        ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E)⟩

end AlgebraicGeometry

end
