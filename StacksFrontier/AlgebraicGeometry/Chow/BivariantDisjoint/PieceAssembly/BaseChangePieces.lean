module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence

/-!
# Assembling a bivariant class from classes on the pieces of a disjoint union decomposition

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `X = ∐_{i ∈ I} X_i` and
`Y = ∐_{j ∈ J} Y_j` be decompositions into open and closed subschemes and let `a : I → J` satisfy
`f(X_i) ⊆ Y_{a(i)}`, so that `f` restricts to `f_i : X_i ⟶ Y_{a(i)}`. **Stacks 0FDZ** asserts

  `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})`.

This file builds the map `Ψ` from right to left and the isomorphism itself. Given a family `(c_i)`
of bivariant classes of degree `p` for the `f_i` and a test scheme `g : T ⟶ Y`, write
`T_j = g^{-1}(Y_j)`; the fibre product `X ×_Y T` then decomposes into the open and closed pieces
`X_i ×_{Y_{a(i)}} T_{a(i)}`, so a class on `X ×_Y T` is the same thing as a family of classes on
those pieces, and one may send `α ∈ A_k(T)` to the class whose restriction to the `i`-th piece is
`c_i ∩ α|_{T_{a(i)}}`. The source proof is exactly this, "because
`CH_{k-p}(X) = ∏_i CH_{k-p}(X_i)`". The map `Φ` from left to right is restriction to the pieces,
built in `StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction`, and the two
round trips are proved here.

## Main definitions

* `Stacks.Chow.pieceImmersion` — the open immersion `X_i ×_{Y_{a(i)}} T_{a(i)} ⟶ X ×_Y T`.
* `Stacks.Chow.testPieceMap`, `Stacks.Chow.piecePullbackMap` — the restrictions of a morphism of
  test schemes, and of a base change of it, to the `i`-th pieces.
* `Stacks.Chow.chowGroupPullbackPieceEquiv` — the product decomposition
  `CH_k(X ×_Y T) = ∏_i CH_k(X_i ×_{Y_{a(i)}} T_{a(i)})`.
* `Stacks.Chow.bivariantPieceAssemblyCap` — **Stacks 0FDZ**, the cap operation assembled from a
  family of bivariant classes on the pieces.
* `Stacks.Chow.IsBivariantPieceAssembly` — the assertion that a bivariant class for `f` is the one
  assembled from a given family of classes on the pieces.
* `Stacks.Chow.ProperPushforwardFactorsOnPieces`,
  `Stacks.Chow.FlatPullbackFactorsOnPieces` — the assertions that Stacks 02S2 and Stacks 02S1
  descend along a base change by an open immersion; see the implementation notes. Both are
  theorems, `Stacks.Chow.properPushforwardFactorsOnPieces` and
  `Stacks.Chow.flatPullbackFactorsOnPieces`.
* `Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction` — the open-immersion case of Stacks
  02TA for a Gysin system, with the invertible module taken on the ambient scheme itself.
* `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp` — the assertion that the Gysin map of a
  system is unchanged when an iterated pullback of an invertible module is replaced by the
  pullback along the composite.
* `Stacks.Chow.zeroSchemePiece`, `Stacks.Chow.zeroSchemePieceImmersion` — the `i`-th piece of the
  zero scheme of the section pulled back to `X ×_Y T`, and its inclusion.
* `Stacks.Chow.chowGroupZeroSchemePieceEquiv` — the product decomposition of the Chow groups of
  that zero scheme along the pieces.
* `Stacks.Chow.zeroSchemeTestPieceIso`, `Stacks.Chow.zeroSchemePieceComparison` — the two
  presentations of the `i`-th piece of the zero scheme on the test scheme, and the induced
  identification of the `i`-th piece of the zero scheme on `X ×_Y T`.
* `Stacks.Chow.bivariantPieceAssembly` — **Stacks 0FDZ**, the assembled class `Ψ((c_i))`.
* `Stacks.Chow.bivariantPieceAssemblyHom` — **Stacks 0FDZ**, the map `Ψ` as a homomorphism of
  groups.
* `Stacks.Chow.bivariantPieceEquiv` — **Stacks 0FDZ**, the isomorphism
  `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})` of the tag.

## Main results

* `Stacks.Chow.opensRange_pieceImmersion` — the image of the `i`-th piece immersion is the
  preimage of `X_i` under the projection `X ×_Y T ⟶ X`.
* `Stacks.Chow.isClopenDecomposition_opensRange_pieceImmersion` — those images decompose
  `X ×_Y T` into open and closed subschemes.
* `Stacks.Chow.isPullback_testPieceMap`, `Stacks.Chow.isPullback_piecePullbackMap`,
  `Stacks.Chow.isPullback_piecePullbackMap_snd` — the three cartesian squares that let the
  naturality axioms of a class on a piece be applied.
* `Stacks.Chow.chowGroupPullbackPieceEquiv_apply` — the components of the product decomposition
  are restriction of Chow classes along the piece immersions.
* `Stacks.Chow.bivariantPieceAssemblyCap_restrict` — the characterizing property of the assembled
  cap operation: its restriction to the `i`-th piece is `c_i ∩ α|_{T_{a(i)}}`.
* `Stacks.Chow.bivariantPieceAssemblyCap_add`, `_neg`, `_zero` — assembling is additive in the
  family of classes on the pieces.
* `Stacks.Chow.eq_of_isBivariantPieceAssembly` — the cap formula determines the assembled class,
  so the map `Ψ` of Stacks 0FDZ is well defined wherever it exists.
* `Stacks.Chow.IsBivariantPieceAssembly.add`, `.neg`, `.zero` — the characterization transports
  along the group operations, which is the assertion that `Ψ` is a homomorphism of groups wherever
  it is defined.
* `Stacks.Chow.bivariantPieceAssemblyCap_proper_naturality`,
  `Stacks.Chow.bivariantPieceAssemblyCap_flat_naturality` — the proper-pushforward and the
  flat-pullback axiom of Stacks 0B76 for the assembled cap operation.
* `Stacks.Chow.bivariantPieceAssemblyCap_gysin_naturality` — the Gysin axiom of Stacks 0B76 for
  the assembled cap operation.
* `Stacks.Chow.zeroScheme_pullback_pullback` — pulling a section back in two steps and pulling it
  back along the composite give the same zero scheme.
* `Stacks.Chow.BivariantClass.cap_chowGroupRestrict` — the cap operation of a bivariant class
  commutes with restricting the test scheme along an open immersion, the flat-pullback axiom of
  Stacks 0B76 in relative dimension zero.
* `Stacks.Chow.isBivariantPieceAssembly_bivariantPieceRestriction` — `Ψ ∘ Φ = id`: a bivariant
  class is the one assembled from its restrictions to the pieces.
* `Stacks.Chow.bivariantPieceRestriction_bivariantPieceAssembly` — `Φ ∘ Ψ = id`: the restriction
  of an assembled class to the `i`-th piece is the `i`-th member of the family.

## Implementation notes

### No `@[stacks]` attribute on the product decomposition of the Chow groups

The identity `CH_k(X) = ∏_i CH_k(X_i)` is used without comment in the proof of Stacks 0FDZ and is
not the statement of that tag, so `Stacks.Chow.chowGroupPullbackPieceEquiv` and the geometric
lemmas it rests on are untagged, following
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup` and
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces`.

### Stacks 02S1 and 02S2 along the legs of a cartesian square are discharged, not carried

Restriction of Chow classes along an open immersion over the base,
`Stacks.Chow.chowGroupRestrict`, is unconditional, and its compatibility with proper pushforward
and with flat pullback in a cartesian square is proved in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward` and
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback`. Stacks 02S1 is proved
in general in this repository, as
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`, exactly as Stacks
02S2 is, as `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`.

Both sides of a naturality axiom for the assembled operation are compared piece by piece, and on
the `i`-th piece the morphism one pushes or pulls along is not `h` itself but its restriction
`Stacks.Chow.testPieceMap`, respectively the restriction `Stacks.Chow.piecePullbackMap` of the
given base change. The axioms of `Stacks.Chow.BivariantClass` quantify over 02S2 and 02S1 *for
the morphisms they mention*, so they supply nothing for those restrictions directly; but the
restrictions are themselves proper, respectively flat and locally of finite type, over the base
(being base changes of `h` along open immersions), so the general theorems above apply to them
outright. The transfer is therefore stated as a theorem rather than a hypothesis, as
`Stacks.Chow.ProperPushforwardFactorsOnPieces` and `Stacks.Chow.FlatPullbackFactorsOnPieces`: the
assertions that 02S2 and 02S1 descend along a base change by an open immersion.

Both are proved — `Stacks.Chow.properPushforwardFactorsOnPieces` and
`Stacks.Chow.flatPullbackFactorsOnPieces` — and substituted below rather than assumed.

### The two Gysin hypotheses, and why both are needed

The Gysin axiom of Stacks 0B76 for the assembled cap operation,
`Stacks.Chow.bivariantPieceAssemblyCap_gysin_naturality`, carries two further `Prop`s about a
`Stacks.Chow.GysinSystem` beyond the open-immersion case of Stacks 02TA that
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction` already carries; both are
of the kind this development carries rather than proves.

Restricted to the `i`-th piece, that axiom has to compare the Gysin map the family supplies with
the one the system supplies on `X_i ×_{Y_{a(i)}} T_{a(i)}`. Two separate comparisons arise.

* Moving a restriction along an open immersion past a Gysin map. On the test scheme the relevant
  open immersion is the inclusion `ι_i` of `T_{a(i)}` in `T`, and the invertible module upstairs
  is `L` itself rather than a pullback, so the form of Stacks 02TA that applies is
  `Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction`. It is incomparable with the form in
  which the module upstairs is a pullback along a structure morphism, for the reason in the next
  item; neither implies the other.
* Reconciling two invertible modules on one scheme. The Gysin axiom of `c_i` is stated for a
  module on the test scheme `T_{a(i)}` of `c_i`, so the module it forms on the piece of `X ×_Y T`
  is `(Scheme.Modules.pullback π_i).obj ((Scheme.Modules.pullback ι_i).obj L)` for the projection
  `π_i` of the piece, whereas restricting the Gysin map on `X ×_Y T` produces
  `(Scheme.Modules.pullback (π_i ≫ ι_i)).obj L`. The two are isomorphic, by
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`, and *not* equal; since
  `Stacks.Chow.GysinSystem.chern` is **data** indexed by the module, the two Gysin maps are a
  priori unrelated. `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp` is exactly the assertion
  that they agree. Note that their zero schemes *are* literally equal, by
  `Stacks.Chow.zeroScheme_pullback_pullback`, so no transport of subschemes is involved — only the
  Gysin map is at issue, and the isomorphism of modules does carry one section to the other, by
  `AlgebraicGeometry.pullbackGlobalSections_comp`.

Both are `Prop`s and both are satisfied by the genuine first Chern class rule, so substituting it
discharges them, exactly as for
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`.

### The two round trips

`Ψ ∘ Φ = id` is the substance of the source proof: on the `i`-th piece it says that `c ∩ -`
commutes with restricting the test scheme to `T_{a(i)}`, which is the flat-pullback axiom of
Stacks 0B76 in relative dimension zero, where flat pullback is restriction of Chow classes
(`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`); the source phrases the same step as flat
pullback followed by proper pushforward along `∐_{a(i) = j} X_i → X`. It carries no hypothesis
beyond the ones already listed, because Stacks 02S1 along an open immersion is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion`.

`Φ ∘ Ψ = id` is the source's "immediate": by
`Stacks.Chow.bivariantPieceAssemblyCap_restrict` the assembled cap operation restricted to the
`i`-th piece of `X ×_Y (T' ⟶ Y_{a(i)} ⟶ Y)` is `c_i ∩ -`, the only bookkeeping being that the
piece of `T'` lying over `Y_{a(i)}` is the whole of `T'`, so the two presentations of the `i`-th
piece of the base change differ by an isomorphism over `T'`.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

/-! ## This part

The first of the four parts of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`; the overview above covers
all four. This part treats the pieces `X_i ×_{Y_{a(i)}} T_{a(i)}` of a base change and their
inclusions, the restrictions of a morphism of test schemes and of a base change of it to the
pieces, the product decomposition of the Chow groups of a base change along the pieces, the
descent of Stacks 02S2 and 02S1 along a base change by an open immersion, the two Gysin hypotheses
`Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction` and
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp`, and the axioms of a bivariant class at a
test morphism presented by an equality. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The pieces of a base change -/

section Geometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) {T : Scheme.{u}} (g : T ⟶ Y)

/-- The base-change map `X ×_{Y_{a(i)}} T_{a(i)} ⟶ X ×_Y T` induced by the inclusion of the piece
`T_{a(i)} = g^{-1}(Y_{a(i)})` of the test scheme, the source being the fibre product along the
restricted test morphism `T_{a(i)} ⟶ Y_{a(i)}` followed by the inclusion of `Y_{a(i)}`. -/
def pieceBaseChangeMap (i : I) :
    pullback f (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι) ⟶ pullback f g :=
  pullback.map f (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι) f g (𝟙 X)
    ((g ⁻¹ᵁ UY (a i)).ι) (𝟙 Y) (by simp) (by simp)

/-- The base-change map `pieceBaseChangeMap` is an open immersion. -/
instance isOpenImmersion_pieceBaseChangeMap (i : I) :
    IsOpenImmersion (pieceBaseChangeMap f UY a g i) := by
  rw [pieceBaseChangeMap]; infer_instance

/-- The base-change map is compatible with the projections to `X`. -/
@[simp, reassoc]
theorem pieceBaseChangeMap_fst (i : I) :
    pieceBaseChangeMap f UY a g i ≫ pullback.fst f g =
      pullback.fst f (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι) := by
  simp [pieceBaseChangeMap]

/-- The base-change map is compatible with the projections to the test scheme. -/
@[simp, reassoc]
theorem pieceBaseChangeMap_snd (i : I) :
    pieceBaseChangeMap f UY a g i ≫ pullback.snd f g =
      pullback.snd f (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι) ≫
        (g ⁻¹ᵁ UY (a i)).ι := by
  simp [pieceBaseChangeMap]

/-- The base-change map is, up to the canonical identifications of iterated fibre products, the
projection exhibiting `X ×_{Y_{a(i)}} T_{a(i)}` as the base change of `T_{a(i)} ⊆ T` along
`X ×_Y T ⟶ T`. -/
theorem pieceBaseChangeMap_eq_comp (i : I) :
    pieceBaseChangeMap f UY a g i =
      ((pullback.congrHom (rfl : f = f)
            (Scheme.Hom.resLE_comp_ι g (le_rfl : g ⁻¹ᵁ UY (a i) ≤ g ⁻¹ᵁ UY (a i)))).trans
          (pullbackLeftPullbackSndIso f g (g ⁻¹ᵁ UY (a i)).ι).symm).hom ≫
        pullback.fst (pullback.snd f g) (g ⁻¹ᵁ UY (a i)).ι := by
  apply pullback.hom_ext <;> simp [pieceBaseChangeMap]

/-- The image of the base-change map is the preimage of the piece `T_{a(i)}` of the test scheme
under the projection `X ×_Y T ⟶ T`. -/
theorem opensRange_pieceBaseChangeMap (i : I) :
    (pieceBaseChangeMap f UY a g i).opensRange = pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ UY (a i)) := by
  set e := ((pullback.congrHom (rfl : f = f)
      (Scheme.Hom.resLE_comp_ι g (le_rfl : g ⁻¹ᵁ UY (a i) ≤ g ⁻¹ᵁ UY (a i)))).trans
    (pullbackLeftPullbackSndIso f g (g ⁻¹ᵁ UY (a i)).ι).symm) with he
  have hsurj : Function.Surjective e.hom.base := fun y ↦
    ⟨e.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
  refine Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, pieceBaseChangeMap_eq_comp, ← he, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
    IsOpenImmersion.range_pullbackFst (g ⁻¹ᵁ UY (a i)).ι (pullback.snd f g)]
  simp

/-- The open immersion `X_i ×_{Y_{a(i)}} T_{a(i)} ⟶ X ×_Y T` cutting out the `i`-th piece of the
base change: the comparison of `Stacks.Chow.pieceComparison` at the restricted test morphism,
followed by the base change of the inclusion of the piece `T_{a(i)}` of the test scheme. -/
def pieceImmersion (i : I) :
    pullback (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ⟶
      pullback f g :=
  pieceComparison f UX UY a ha i (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
    pieceBaseChangeMap f UY a g i

/-- The piece immersion `pieceImmersion` is an open immersion. -/
instance isOpenImmersion_pieceImmersion (i : I) :
    IsOpenImmersion (pieceImmersion f UX UY a ha g i) := by
  rw [pieceImmersion]; infer_instance

/-- The piece immersion is compatible with the projections to `X`: it carries the projection of
the piece, followed by the inclusion of `X_i`, to the projection of `X ×_Y T`. -/
@[simp, reassoc]
theorem pieceImmersion_comp_fst (i : I) :
    pieceImmersion f UX UY a ha g i ≫ pullback.fst f g =
      pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        (UX i).ι := by
  simp [pieceImmersion]

/-- The image of the `i`-th piece immersion is the preimage of the piece `X_i` under the
projection `X ×_Y T ⟶ X`.

The comparison cuts out the preimage of `X_i` inside `X ×_{Y_{a(i)}} T_{a(i)}`, whose image in
`X ×_Y T` is the preimage of `T_{a(i)}`; the two intersect in the preimage of `X_i`, because
`X_i ⊆ f^{-1}(Y_{a(i)})` forces a point of `X ×_Y T` lying over `X_i` to lie over
`T_{a(i)}`. -/
theorem opensRange_pieceImmersion (i : I) :
    (pieceImmersion f UX UY a ha g i).opensRange = pullback.fst f g ⁻¹ᵁ UX i := by
  have hle : pullback.fst f g ⁻¹ᵁ UX i ≤ pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ UY (a i)) := by
    calc pullback.fst f g ⁻¹ᵁ UX i
        ≤ pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ UY (a i)) := (pullback.fst f g).preimage_mono (ha i)
      _ = pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ UY (a i)) := by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have hpre : pullback.fst f (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl ≫ (UY (a i)).ι) ⁻¹ᵁ
      UX i = pieceBaseChangeMap f UY a g i ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ UX i) := by
    rw [← Scheme.Hom.comp_preimage, pieceBaseChangeMap_fst]
  have hcomp : (pieceImmersion f UX UY a ha g i).opensRange =
      (pieceComparison f UX UY a ha i (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        pieceBaseChangeMap f UY a g i).opensRange := rfl
  rw [hcomp, Scheme.Hom.opensRange_comp, opensRange_pieceComparison, hpre,
    Scheme.Hom.image_preimage_eq_opensRange_inf, opensRange_pieceBaseChangeMap,
    inf_eq_right.mpr hle]

/-- The images of the piece immersions decompose the base change `X ×_Y T` into open and closed
subschemes: they are the preimages of the pieces of `X` under the projection to `X`. -/
theorem isClopenDecomposition_opensRange_pieceImmersion (hX : IsClopenDecomposition UX) :
    IsClopenDecomposition fun i ↦ (pieceImmersion f UX UY a ha g i).opensRange := by
  simp only [opensRange_pieceImmersion]
  exact hX.preimage (pullback.fst f g)

/-- The piece immersion is compatible with the projections to the test scheme: it carries the
projection of the piece, followed by the inclusion of `T_{a(i)}`, to the projection of
`X ×_Y T`. -/
@[simp, reassoc]
theorem pieceImmersion_comp_snd (i : I) :
    pieceImmersion f UX UY a ha g i ≫ pullback.snd f g =
      pullback.snd (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        (g ⁻¹ᵁ UY (a i)).ι := by
  simp [pieceImmersion, opensPullbackComparison_snd_assoc]

/-- The `i`-th piece immersion factors through the base change along the inclusion of the piece
`T_{a(i)}` of the test scheme: it is the comparison at the restricted test morphism followed by
that base change. -/
theorem pieceImmersion_eq_pieceComparisonCongr_comp (i : I) :
    pieceImmersion f UX UY a ha g i =
      pieceComparisonCongr f UX UY a ha i (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
          ((g ⁻¹ᵁ UY (a i)).ι ≫ g) (Scheme.Hom.resLE_comp_ι g le_rfl) ≫
        bivariantBaseChangeMap f g (g ⁻¹ᵁ UY (a i)).ι := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp [pieceComparisonCongr_snd_assoc]

end Geometry

/-- The canonical map between two base changes of `f` along a morphism of test schemes is an open
immersion as soon as that morphism is: it is a base change of it. -/
instance isOpenImmersion_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (q : T' ⟶ T) [IsOpenImmersion q] : IsOpenImmersion (bivariantBaseChangeMap f g q) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_bivariantBaseChangeMap f g q) inferInstance

/-! ### Morphisms of test schemes -/

section TestMorphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) {T T' : Scheme.{u}} (g : T ⟶ Y) (h : T' ⟶ T)

/-- The restriction `T'_{a(i)} ⟶ T_{a(i)}` of a morphism `h : T' ⟶ T` of test schemes to the
pieces lying over `Y_{a(i)}`, the piece of `T'` being taken with respect to the composite test
morphism `h ≫ g`. -/
def testPieceMap (i : I) :
    ((h ≫ g) ⁻¹ᵁ UY (a i) : Scheme.{u}) ⟶ ((g ⁻¹ᵁ UY (a i) : Scheme.{u})) :=
  h.resLE (g ⁻¹ᵁ UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl

/-- The restriction to the pieces is the restriction of `h`: it agrees with `h` after composing
with the two piece inclusions. -/
@[simp, reassoc]
theorem testPieceMap_comp_ι (i : I) :
    testPieceMap UY a g h i ≫ (g ⁻¹ᵁ UY (a i)).ι = ((h ≫ g) ⁻¹ᵁ UY (a i)).ι ≫ h :=
  Scheme.Hom.resLE_comp_ι h le_rfl

/-- The restriction to the pieces lies over `Y_{a(i)}`: composed with the restricted test
morphism of `T` it is the restricted test morphism of `T'`. -/
@[simp, reassoc]
theorem testPieceMap_comp_resLE (i : I) :
    testPieceMap UY a g h i ≫ g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl =
      (h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl :=
  Scheme.Hom.resLE_comp_resLE h le_rfl g le_rfl

/-- The piece of `T'` over `Y_{a(i)}` is the inverse image under `h` of the piece of `T`: the
square of the two piece inclusions and the two restrictions of `h` is cartesian. -/
theorem isPullback_testPieceMap (i : I) :
    IsPullback (((h ≫ g) ⁻¹ᵁ UY (a i)).ι) (testPieceMap UY a g h i) h ((g ⁻¹ᵁ UY (a i)).ι) :=
  (AlgebraicGeometry.IsOpenImmersion.isPullback (testPieceMap UY a g h i)
    (((h ≫ g) ⁻¹ᵁ UY (a i)).ι) ((g ⁻¹ᵁ UY (a i)).ι) h
    (testPieceMap_comp_ι UY a g h i).symm (by simp)).flip

variable (h' : pullback f (h ≫ g) ⟶ pullback f g)
  (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g))

/-- The `i`-th piece of `X ×_Y T'` is the preimage under `h'` of the `i`-th piece of `X ×_Y T`. -/
private theorem opensRange_pieceImmersion_comp_eq_preimage
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (i : I) :
    h' ⁻¹ᵁ (pieceImmersion f UX UY a ha g i).opensRange =
      (pieceImmersion f UX UY a ha (h ≫ g) i).opensRange := by
  rw [opensRange_pieceImmersion, opensRange_pieceImmersion, ← Scheme.Hom.comp_preimage, hfst]

include hfst in
/-- A base change of a morphism of test schemes carries the `i`-th piece of `X ×_Y T'` into the
`i`-th piece of `X ×_Y T`, both pieces being the inverse images of `X_i`. -/
theorem range_pieceImmersion_comp_subset (i : I) :
    Set.range (pieceImmersion f UX UY a ha (h ≫ g) i ≫ h').base ⊆
      Set.range (pieceImmersion f UX UY a ha g i).base := by
  rintro _ ⟨y, rfl⟩
  have hy : (pieceImmersion f UX UY a ha (h ≫ g) i).base y ∈
      h' ⁻¹ᵁ (pieceImmersion f UX UY a ha g i).opensRange := by
    rw [opensRange_pieceImmersion_comp_eq_preimage f UX UY a ha g h h' hfst i]
    exact ⟨y, rfl⟩
  exact hy

/-- The restriction of a base change `h' : X ×_Y T' ⟶ X ×_Y T` of a morphism of test schemes to
the `i`-th pieces, obtained from the universal property of the open immersion cutting out the
`i`-th piece of `X ×_Y T`. -/
def piecePullbackMap (i : I) :
    pullback (pieceMap f UX UY a ha i)
        ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ⟶
      pullback (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) :=
  IsOpenImmersion.lift (pieceImmersion f UX UY a ha g i)
    (pieceImmersion f UX UY a ha (h ≫ g) i ≫ h')
    (range_pieceImmersion_comp_subset f UX UY a ha g h h' hfst i)

/-- The restriction to the pieces lies over the base change: the square of the two piece
immersions and the two base changes commutes. -/
@[reassoc]
theorem piecePullbackMap_comp_pieceImmersion (i : I) :
    piecePullbackMap f UX UY a ha g h h' hfst i ≫ pieceImmersion f UX UY a ha g i =
      pieceImmersion f UX UY a ha (h ≫ g) i ≫ h' :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restriction to the pieces is compatible with the projections to `X_i`. -/
@[reassoc]
theorem piecePullbackMap_comp_fst (i : I) :
    piecePullbackMap f UX UY a ha g h h' hfst i ≫
        pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
      pullback.fst (pieceMap f UX UY a ha i)
        ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) := by
  rw [← cancel_mono (UX i).ι, Category.assoc,
    ← pieceImmersion_comp_fst f UX UY a ha g i,
    ← pieceImmersion_comp_fst f UX UY a ha (h ≫ g) i,
    piecePullbackMap_comp_pieceImmersion_assoc, hfst]

include hfst in
/-- The restriction to the pieces is compatible with the projections to the pieces of the test
schemes. -/
theorem piecePullbackMap_comp_snd
    (hsnd : pullback.snd f (h ≫ g) ≫ h = h' ≫ pullback.snd f g) (i : I) :
    piecePullbackMap f UX UY a ha g h h' hfst i ≫
        pullback.snd (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
      pullback.snd (pieceMap f UX UY a ha i)
          ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
        testPieceMap UY a g h i := by
  rw [← cancel_mono (g ⁻¹ᵁ UY (a i)).ι, Category.assoc,
    ← pieceImmersion_comp_snd f UX UY a ha g i, ← Category.assoc,
    piecePullbackMap_comp_pieceImmersion, Category.assoc, ← hsnd, ← Category.assoc,
    pieceImmersion_comp_snd, Category.assoc, Category.assoc, testPieceMap_comp_ι]

include hfst in
/-- The `i`-th piece of `X ×_Y T'` is the inverse image of the `i`-th piece of `X ×_Y T` under a
base change `h'` of a morphism of test schemes: the square of the two piece immersions and the
two base changes is cartesian. -/
theorem isPullback_piecePullbackMap (i : I) :
    IsPullback (pieceImmersion f UX UY a ha (h ≫ g) i)
      (piecePullbackMap f UX UY a ha g h h' hfst i) h' (pieceImmersion f UX UY a ha g i) :=
  (AlgebraicGeometry.IsOpenImmersion.isPullback
    (piecePullbackMap f UX UY a ha g h h' hfst i)
    (pieceImmersion f UX UY a ha (h ≫ g) i) (pieceImmersion f UX UY a ha g i) h'
    (piecePullbackMap_comp_pieceImmersion f UX UY a ha g h h' hfst i).symm
    (opensRange_pieceImmersion_comp_eq_preimage f UX UY a ha g h h' hfst i)).flip

include hfst in
/-- The `i`-th piece of `X ×_Y T'` is the fibre product of the `i`-th piece of `X ×_Y T` with the
`i`-th piece of `T'` over the `i`-th piece of `T`. -/
theorem isPullback_piecePullbackMap_snd
    (hsnd : pullback.snd f (h ≫ g) ≫ h = h' ≫ pullback.snd f g) (i : I) :
    IsPullback (pullback.snd (pieceMap f UX UY a ha i)
        ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl))
      (piecePullbackMap f UX UY a ha g h h' hfst i) (testPieceMap UY a g h i)
      (pullback.snd (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)) := by
  refine IsPullback.of_bot ?_
    (piecePullbackMap_comp_snd f UX UY a ha g h h' hfst hsnd i).symm
    (IsPullback.of_hasPullback (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)).flip
  rw [piecePullbackMap_comp_fst, testPieceMap_comp_resLE]
  exact (IsPullback.of_hasPullback (pieceMap f UX UY a ha i)
    ((h ≫ g).resLE (UY (a i)) ((h ≫ g) ⁻¹ᵁ UY (a i)) le_rfl)).flip

end TestMorphism

/-! ### The Chow groups of a base change decompose along the pieces -/

section ChowPieces

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (hX : IsClopenDecomposition UX)
  {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The piece immersion is a morphism over the base: it carries the structure morphism of
`X ×_Y T` to the structure morphism of the `i`-th piece, taken through the inclusion of `X_i`. -/
theorem pieceImmersion_comp_structureMorphism (i : I) :
    pieceImmersion f UX UY a ha g i ≫ (pullback.fst f g ≫ sX) =
      pullback.fst (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
        ((UX i).ι ≫ sX) := by
  rw [← Category.assoc, pieceImmersion_comp_fst, Category.assoc]

/-- **`CH_k(X ×_Y T) = ∏_i CH_k(X_i ×_{Y_{a(i)}} T_{a(i)})`.** The Chow groups of a base change of
`f` decompose along the pieces of the decomposition of `X`, the components being restriction of
Chow classes along the piece immersions.

This is `Stacks.Chow.chowGroupClopenRestrictEquiv` for the decomposition of `X ×_Y T` into open
and closed subschemes supplied by
`Stacks.Chow.isClopenDecomposition_opensRange_pieceImmersion`; it is the identity that the proof
of Stacks 0FDZ uses without comment. -/
def chowGroupPullbackPieceEquiv (k : ℤ) :
    chowGroup C (pullback.fst f g ≫ sX) k ≃+
      ∀ i, chowGroup C (pullback.fst (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) k :=
  chowGroupClopenRestrictEquiv C (pullback.fst f g ≫ sX)
    (fun i ↦ pullback.fst (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
    (fun i ↦ pieceImmersion f UX UY a ha g i)
    (fun i ↦ pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i)
    (isClopenDecomposition_opensRange_pieceImmersion f UX UY a ha g hX) k

omit [LocallyOfFiniteType f] in
/-- The components of the product decomposition of the Chow groups of a base change are
restriction of Chow classes along the piece immersions. -/
@[simp]
theorem chowGroupPullbackPieceEquiv_apply (k : ℤ)
    (α : chowGroup C (pullback.fst f g ≫ sX) k) (i : I) :
    chowGroupPullbackPieceEquiv C sX f UX UY a ha hX g k α i =
      chowGroupRestrict C (pullback.fst f g ≫ sX)
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))
        (pieceImmersion f UX UY a ha g i)
        (pieceImmersion_comp_structureMorphism C sX f UX UY a ha g i) k α :=
  chowGroupClopenRestrictEquiv_apply C (pullback.fst f g ≫ sX) _ _ _ _ k α i

end ChowPieces

/-! ### Heterogeneous equalities of Chow classes -/

/-- A heterogeneous equality between elements of a family indexed by the degree may be checked
after applying a degreewise injective map. -/
theorem heq_of_injective_heq {A B : ℤ → Type u} (F : ∀ n, A n → B n)
    (hF : ∀ n, Function.Injective (F n)) {i j : ℤ} (hij : i = j) {x : A i} {y : A j}
    (hxy : HEq (F i x) (F j y)) : HEq x y := by
  cases hij
  exact heq_of_eq (hF _ (eq_of_heq hxy))

/-- A heterogeneous equality between families of Chow classes may be checked componentwise. -/
theorem heq_pi_of_heq {K : Type u} {A : ℤ → K → Type u} {i j : ℤ} (hij : i = j)
    {x : ∀ t, A i t} {y : ∀ t, A j t} (hxy : ∀ t, HEq (x t) (y t)) : HEq x y := by
  cases hij
  exact heq_of_eq (funext fun t ↦ eq_of_heq (hxy t))

/-! ### Stacks 02S2 and 02S1 along the legs of a cartesian square -/

/-- The assertion that Stacks 02S2 descends to base changes along open immersions: whenever
proper pushforward along the proper leg `q` of a cartesian square with open-immersion horizontals
factors through rational equivalence, so does proper pushforward along the opposite leg `q'`.

It is a theorem, `Stacks.Chow.properPushforwardFactorsOnPieces`, and is named here only to
abbreviate the descent statement. -/
def ProperPushforwardFactorsOnPieces (C : ChowSituation.{u}) : Prop :=
  ∀ {A B A' B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA)
    (mA : A' ⟶ A) [IsOpenImmersion mA] (_hmA : mA ≫ sA = sA')
    (mB : B' ⟶ B) [IsOpenImmersion mB] (_hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') (hq' : q' ≫ sB' = sA') (hsq : IsPullback mA q' q mB) (k : ℤ),
    letI : IsProper q' := isProper_of_isPullback q mA mB q' hsq
    ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k →
      ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' q' hq' k

/-- **Stacks 02S2 descends to base changes along open immersions.** Proper pushforward along the
opposite leg `q'` of a cartesian square with open-immersion horizontals factors through rational
equivalence: `q'` is proper over the base, being a base change of the proper `q`, and Stacks 02S2
holds for every proper morphism over the base.

The hypothesis offered for `q` is therefore not used; the conclusion for `q'` is
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence` outright. -/
theorem properPushforwardFactorsOnPieces (C : ChowSituation.{u}) :
    ProperPushforwardFactorsOnPieces C := by
  intro A B A' B' sA _ sB _ sA' _ sB' _ q _ hq mA _ hmA mB _ hmB q' hq' hsq k
  have : IsProper q' := isProper_of_isPullback q mA mB q' hsq
  intro _
  exact properPushforwardFactorsThroughRationalEquivalence C sA' sB' q' hq' k

/-- The assertion that Stacks 02S1 descends to base changes along open immersions: whenever flat
pullback along the flat leg `q` of a cartesian square with open-immersion horizontals factors
through rational equivalence, so does flat pullback along the opposite leg `q'`.

It is a theorem, `Stacks.Chow.flatPullbackFactorsOnPieces`, named here only to abbreviate the
descent statement, exactly as for `Stacks.Chow.ProperPushforwardFactorsOnPieces`: Stacks 02S1 is
proved in general in this repository, as
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, so the hypothesis offered for
`q` is not needed and the conclusion for `q'` is supplied outright. -/
def FlatPullbackFactorsOnPieces (C : ChowSituation.{u}) : Prop :=
  ∀ {A B A' B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (mA : A' ⟶ A) [IsOpenImmersion mA] (_hmA : mA ≫ sA = sA')
    (mB : B' ⟶ B) [IsOpenImmersion mB] (_hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') (hq' : q' ≫ sB' = sA') (hsq : IsPullback mA q' q mB) (k : ℤ),
    letI : LocallyOfFiniteType q' :=
      MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat q' := MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
    ∀ hr' : AlgebraicGeometry.RelativeDimension q' r,
      FlatPullbackFactorsThroughRationalEquivalence C sA sB q hq r hr k →
        FlatPullbackFactorsThroughRationalEquivalence C sA' sB' q' hq' r hr' k

/-- **Stacks 02S1 descends to base changes along open immersions.** Flat pullback along the
opposite leg `q'` of a cartesian square with open-immersion horizontals factors through rational
equivalence: `q'` is flat and locally of finite type over the base, being a base change of such a
`q`, and Stacks 02S1 holds for every such morphism over the base, in any relative dimension it
has.

The hypotheses offered for `q` are therefore not used; the conclusion for `q'` is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` outright. -/
theorem flatPullbackFactorsOnPieces (C : ChowSituation.{u}) : FlatPullbackFactorsOnPieces C := by
  intro A B A' B' sA _ sB _ sA' _ sB' _ q _ _ hq r hr mA _ hmA mB _ hmB q' hq' hsq k
  have : LocallyOfFiniteType q' :=
    MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
  have : Flat q' := MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
  intro hr' _
  exact flatPullbackFactorsThroughRationalEquivalence_general C sA' sB' q' hq' r hr' k

/-! ### Zero schemes of iterated pullbacks, and the Gysin naturality this forces -/

/-- **Stacks 0B6Y, read along a composite.** Pulling a section back in two steps and pulling it
back along the composite give the *same* zero scheme, even though the two invertible modules
carrying those sections are merely isomorphic: both zero schemes are the inverse image of the
zero scheme downstairs, by `Stacks.Divisors.zeroScheme_pullback` and
`AlgebraicGeometry.Scheme.IdealSheafData.comap_comp`. -/
theorem zeroScheme_pullback_pullback {A B T : Scheme.{u}} (v : A ⟶ B) (w : B ⟶ T)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback w).obj L))
        (AlgebraicGeometry.pullbackGlobalSections v ((Scheme.Modules.pullback w).obj L)
          (AlgebraicGeometry.pullbackGlobalSections w L s)) =
      Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (v ≫ w)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (v ≫ w) L s) := by
  rw [Stacks.Divisors.zeroScheme_pullback v ((Scheme.Modules.pullback w).obj L)
      (AlgebraicGeometry.pullbackGlobalSections w L s),
    Stacks.Divisors.zeroScheme_pullback w L s,
    Stacks.Divisors.zeroScheme_pullback (v ≫ w) L s,
    Scheme.IdealSheafData.comap_comp]

/-- **The open-immersion case of Stacks 02TA for a Gysin system, with the module taken on the
ambient scheme.** For an open immersion `u : A ⟶ B` over the base and an invertible module `L` on
`B` itself with a global section `s`, restriction along `u` carries the Gysin map of `Z(s)` to the
Gysin map of the zero scheme of the section pulled back to `A`.

Like `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` this cannot be derived from
`Stacks.Chow.GysinSystem`: the first Chern class rules a system provides on `A` and on `B` are
unrelated data. It is carried as a hypothesis, and substituting the genuine first Chern class
rule discharges it: `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction`. It is
*not* comparable with the variant in which the module upstairs is itself a pullback, because
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is an isomorphism and not an equality; see the
implementation notes.

As in `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`, the open immersion `j` of the two
zero schemes is constrained by the square of Remark 0B6Y, `j ≫ i = i' ≫ u`, and not only by its
commutativity over the base, which does not determine it. -/
def GysinSystem.IsNaturalUnderOpensRestriction {C : ChowSituation.{u}} (G : GysinSystem C) :
    Prop :=
  ∀ {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (u : A ⟶ B) [IsOpenImmersion u] (hu : u ≫ sB = sA) (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
            (AlgebraicGeometry.pullbackGlobalSections u L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B L s).subscheme)
    [IsOpenImmersion j]
    (_hjsq : j ≫ (Stacks.Divisors.zeroScheme B L s).subschemeι =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB) =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s)).subschemeι ≫ sA)
    (α : chowGroup C sB (k + 1)),
    chowGroupRestrict C ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
          (AlgebraicGeometry.pullbackGlobalSections u L s)).subschemeι ≫ sA) j hj k
        (G.onChow sB L s k α) =
      G.onChow sA ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s) k
        (chowGroupRestrict C sB sA u hu (k + 1) α)

/-- **The Gysin map of a system does not see the difference between an iterated pullback of an
invertible module and the pullback along the composite.** The two modules are isomorphic, by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, and that isomorphism carries one pulled-back
section to the other, by `AlgebraicGeometry.pullbackGlobalSections_comp`; the two zero schemes are
therefore literally equal, by `Stacks.Chow.zeroScheme_pullback_pullback`, and the assertion is
that the two Gysin maps agree under that equality.

`Stacks.Chow.GysinSystem.chern` is **data** indexed by the invertible module, so this does not
follow from `Stacks.Chow.GysinSystem`: it is exactly the statement that the rule a system supplies
is invariant under an isomorphism of invertible modules matching global sections, which the
genuine first Chern class satisfies and an arbitrary rule need not. It is therefore carried as a
hypothesis, in the style of `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`. -/
def GysinSystem.IsNaturalUnderPullbackComp {C : ChowSituation.{u}} (G : GysinSystem C) : Prop :=
  ∀ {A B T : Scheme.{u}} (q : A ⟶ C.S) [LocallyOfFiniteType q] (v : A ⟶ B) (w : B ⟶ T)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C q (k + 1)),
    chowGroupRestrict C
        ((Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback w).obj L))
          (AlgebraicGeometry.pullbackGlobalSections v ((Scheme.Modules.pullback w).obj L)
            (AlgebraicGeometry.pullbackGlobalSections w L s))).subschemeι ≫ q)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (v ≫ w)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (v ≫ w) L s)).subschemeι ≫ q)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (zeroScheme_pullback_pullback v w L s).symm))
        (by rw [← Category.assoc,
          subschemeι_eqToHom (zeroScheme_pullback_pullback v w L s).symm]) k
        (G.onChow q ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback w).obj L))
          (AlgebraicGeometry.pullbackGlobalSections v ((Scheme.Modules.pullback w).obj L)
            (AlgebraicGeometry.pullbackGlobalSections w L s)) k α) =
      G.onChow q ((Scheme.Modules.pullback (v ≫ w)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (v ≫ w) L s) k α

/-! ### The axioms of a bivariant class at a test morphism presented by an equality -/

section OfEq

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- The proper-pushforward axiom of a bivariant class, read at a test morphism presented by an
equality rather than as a literal composite. This is what makes the axiom applicable when the
test morphism arrives as the restriction of a morphism to a piece. -/
theorem BivariantClass.proper_naturality_of_eq (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (q : T' ⟶ T) [IsProper q]
    (m : T' ⟶ Y) [LocallyOfFiniteType m] (hm : q ≫ g = m)
    (q' : pullback f m ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f m) q' q (pullback.snd f g))
    (hfst : q' ≫ pullback.fst f g = pullback.fst f m) (k : ℤ)
    (hqY : q ≫ (g ≫ sY) = m ≫ sY) :
    letI : IsProper q' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (m ≫ sY) (g ≫ sY) q hqY k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f m ≫ sX)
        (pullback.fst f g ≫ sX) q' (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C (m ≫ sY) k),
      c.cap g k (properChowPushforward C (m ≫ sY) (g ≫ sY) q hqY k hfac α) =
        properChowPushforward C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX) q'
          (by rw [← Category.assoc, hfst]) (k - p) hfac' (c.cap m k α) := by
  subst hm
  intro hfac hfac' α
  exact c.proper_naturality g q q' sq hfst k hfac hfac' α

/-- The flat-pullback axiom of a bivariant class, read at a test morphism presented by an
equality rather than as a literal composite. -/
theorem BivariantClass.flat_naturality_of_eq (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (q : T' ⟶ T)
    [LocallyOfFiniteType q] [Flat q] (m : T' ⟶ Y) [LocallyOfFiniteType m] (hm : q ≫ g = m)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (q' : pullback f m ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f m) q' q (pullback.snd f g))
    (hfst : q' ≫ pullback.fst f g = pullback.fst f m) (k : ℤ)
    (hqY : q ≫ (g ≫ sY) = m ≫ sY) :
    letI : LocallyOfFiniteType q' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat q' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension q' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C (m ≫ sY) (g ≫ sY) q hqY r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst f m ≫ sX)
        (pullback.fst f g ≫ sX) q' (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (g ≫ sY) k),
      HEq
        (c.cap m (k + (r : ℤ)) (flatPullbackChow C (m ≫ sY) (g ≫ sY) q hqY r hr k hfac α))
        (flatPullbackChow C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX) q'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac' (c.cap g k α)) := by
  subst hm
  intro hr' hfac hfac' α
  exact c.flat_naturality g q r hr q' sq hfst k hr' hfac hfac' α

end OfEq

end Stacks.Chow

end
