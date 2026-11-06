module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StandardOpenSideCondition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence is tested on every compatible pair of affine opens

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of the
derived category of `𝒪_X`-modules. Relative `m`-pseudo-coherence of `E` asks for *some* affine
open cover of `S` and, over each of its members, *some* affine open cover of its inverse image on
which the equivalent conditions of Stacks 09VC hold. This file proves that the conditions then
hold on *every* compatible pair of affine opens, which is Stacks 09UJ, and deduces that relative
`m`-pseudo-coherence is inherited by the restriction of `f` to compatible open subschemes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair`: **Stacks 09UJ**, the
  equivalence of relative `m`-pseudo-coherence with the condition at every compatible pair of
  affine opens.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.resLE`: the final assertion of Stacks 09UJ,
  that relative `m`-pseudo-coherence survives restriction to compatible open subschemes.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion`: the
  per-pair condition holds at *every* closed immersion of `U` into an affine space over `V`, by
  Stacks 09VC. This is what lets two objects with separately chosen witnesses be compared at one
  common closed immersion.

## Implementation notes

The implication from the condition at every affine pair is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`; all the work is in the
other one, and it is organised around the predicate of Stacks 09VD and 09VE on a morphism of
affine schemes: the existence of *some* closed immersion into a finite-dimensional affine space
over the target along which the derived pushforward of the object is `m`-pseudo-coherent. Four
moves on that predicate are needed:

* `AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_restrict_affineOpen`: shrink the
  source to an affine open. This is Stacks 09VD
  (`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict`) at the
  standard open `⊤ = D(1)` of the base.
* `AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_openSource`: the same along an
  open immersion of the source which need not be the inclusion of an open subscheme, which is
  what lets the moves be chained at a scheme of the form `B ⊆ U` for `B` an affine open of an
  affine open `U` of `X`.
* `AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_shrinkBase`: shrink the base
  along an open immersion through which the structure morphism factors.
* `AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_basicOpenBase`: enlarge the base
  from a standard open back to the whole affine scheme — Stacks 09VD again, this time at the
  affine open `⊤` of the source.

Shrinking the base is where the base change `𝔸ⁿ_W = 𝔸ⁿ_S ×_S W` enters, and it is kept free of
any derived-functor base-change theorem: the closed immersion `i : X ⟶ 𝔸ⁿ_S` factors through the
*open* subscheme `𝔸ⁿ_W ⊆ 𝔸ⁿ_S`, so
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict` already
restricts the condition to it. That factorisation, together with the transport of the condition,
is `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_factor`, stated
for an arbitrary open immersion of the target.

The argument itself is the source's. Given an arbitrary affine pair `U ⊆ f ⁻¹ᵁ V`, every point of
`U` lies in a member `P` of the given cover of the inverse image of a member `T` of the given
cover of `S`, and its image in `V` lies in a standard open `D(r) ⊆ V` contained in `ι_V⁻¹T`. On
an affine open `B` of `U` inside `ι_U⁻¹P ∩ (f|_U)⁻¹D(r)` the four moves carry the condition from
`(P ⟶ T, E|_P)` to `(B ⟶ V, E|_B)`: shrink the source from `P` to `B`, shrink the base from `T`
to `D(r)`, enlarge it from `D(r)` to `V`. Finitely many standard opens of `U` of this kind cover
`U`, because `U` is affine hence quasi-compact, and Stacks 09VE
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_standardCover`) glues
them.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.3 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.4 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Affine space over an open subscheme is an open subscheme of affine space -/

/-- Affine space over an open subscheme of `T` is an open subscheme of affine space over `T`,
because `𝔸ⁿ_S ⟶ 𝔸ⁿ_T` is the base change of `S ⟶ T` along `𝔸ⁿ_T ⟶ T`
(`AlgebraicGeometry.AffineSpace.isPullback_map`). -/
public instance isOpenImmersion_affineSpace_map {n : Type u} {S T : Scheme.{u}} (b : S ⟶ T)
    [IsOpenImmersion b] : IsOpenImmersion (AffineSpace.map n b) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) b).flip ‹IsOpenImmersion b›

/-- Affine space over an isomorphic base is isomorphic, by the same base change. -/
public instance isIso_affineSpace_map {n : Type u} {S T : Scheme.{u}} (b : S ⟶ T) [IsIso b] :
    IsIso (AffineSpace.map n b) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) b).flip ‹IsIso b›

/-- The open subscheme of `𝔸ⁿ_T` that affine space over an open subscheme `S ⊆ T` is: the
inverse image of `S` under the structure morphism. -/
public theorem opensRange_affineSpace_map {n : Type u} {S T : Scheme.{u}} (b : S ⟶ T)
    [IsOpenImmersion b] :
    (AffineSpace.map n b).opensRange = (AffineSpace.over n T).hom ⁻¹ᵁ b.opensRange := by
  have h : IsPullback (AffineSpace.map n b) (AffineSpace.over n S).hom
      (AffineSpace.over n T).hom b := AffineSpace.isPullback_map b
  calc (AffineSpace.map n b).opensRange
      = (h.isoPullback.hom ≫ pullback.fst (AffineSpace.over n T).hom b).opensRange :=
        Opens.ext (congrArg (fun q : AffineSpace n S ⟶ AffineSpace n T => Set.range q.base)
          h.isoPullback_hom_fst.symm)
    _ = (pullback.fst (AffineSpace.over n T).hom b).opensRange :=
        Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = (AffineSpace.over n T).hom ⁻¹ᵁ b.opensRange := Scheme.Hom.opensRange_pullbackFst _ _

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-! ### Moving the local condition of Stacks 09UI across isomorphisms -/

/-- The local condition of Stacks 09UI at a closed immersion out of an open subscheme `U` whose
inclusion happens to be an isomorphism, transported to the ambient scheme.

Pushing forward along `ι_U⁻¹` is restricting along `ι_U`
(`AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv`), so the object
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_isIso_iff` asks
for is the restriction of `E` to `U` that the hypothesis speaks of. -/
public theorem isPseudoCoherentFromAfterPushforward_precomp_inv_ι {X Y : Scheme.{u}}
    (U : X.Opens) [IsIso U.ι] (l : U.toScheme ⟶ Y) [IsClosedImmersion l]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterPushforward l
      ((restrictFunctor U.ι).mapDerivedCategory.obj E) m) :
    IsPseudoCoherentFromAfterPushforward (inv U.ι ≫ l) E m := by
  rw [isPseudoCoherentFromAfterPushforward_precomp_isIso_iff]
  exact IsPseudoCoherentFromAfterPushforward.of_iso l h
    ((Functor.mapDerivedCategoryCongr (pushforwardIsoRestrictInv (inv U.ι) ≪≫
      restrictFunctorCongr (IsIso.inv_inv (f := U.ι)))).app E).symm

/-- For `a : X' ⟶ X` an open immersion, pushing the restriction of `E` along `a` forward along the
isomorphism `X' ≅ ι_a` of `AlgebraicGeometry.Scheme.Hom.isoOpensRange` gives the restriction of
`E` to the open subscheme `ι_a`.

Pushing forward along an isomorphism is restricting along its inverse
(`AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv`), and the two restrictions compose
to the restriction along `ι_a` because the inverse isomorphism followed by `a` is the inclusion
of the image. -/
public def derivedRestrictIsoOpensRangeIso {X X' : Scheme.{u}} (a : X' ⟶ X) [IsOpenImmersion a]
    (E : DerivedCategory X.Modules) :
    (pushforward a.isoOpensRange.hom).mapDerivedCategory.obj
        ((restrictFunctor a).mapDerivedCategory.obj E) ≅
      (restrictFunctor a.opensRange.ι).mapDerivedCategory.obj E :=
  (Functor.mapDerivedCategoryCongr (pushforwardIsoRestrictInv a.isoOpensRange.hom)).app
      ((restrictFunctor a).mapDerivedCategory.obj E) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _ ≪≫ Functor.mapDerivedCategoryCongr
      ((restrictFunctorComp (inv a.isoOpensRange.hom) a).symm ≪≫
        restrictFunctorCongr ((IsIso.inv_comp_eq _).2 (a.isoOpensRange_hom_ι).symm))).app E

/-- **Factoring a closed immersion through an open subscheme of its target, with the local
condition of Stacks 09UI.** Let `i : X ⟶ Y` be a closed immersion whose image lies in the image
of an open immersion `q : Y' ⟶ Y`. Then `i` factors through `q` by a closed immersion along which
the derived pushforward of `E` is `m`-pseudo-coherent as soon as it is along `i`.

Restricting the target of `i` to the image of `q` keeps the condition, by
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict`; the
hypothesis makes `ι` of the inverse image an isomorphism, so the restricted closed immersion is
the required factorisation up to isomorphisms on both sides, which
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_inv_ι` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff`
absorb. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_factor {X Y Y' : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (q : Y' ⟶ Y) [IsOpenImmersion q]
    (hi : i ⁻¹ᵁ q.opensRange = ⊤) (E : DerivedCategory X.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ j : X ⟶ Y', IsClosedImmersion j ∧ j ≫ q = i ∧
      IsPseudoCoherentFromAfterPushforward j E m := by
  set O : Y.Opens := q.opensRange
  have htop : (i ⁻¹ᵁ O).ι.opensRange = ⊤ := by rw [Scheme.Opens.opensRange_ι]; exact hi
  have hiso : IsIso (i ⁻¹ᵁ O).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  have hcl : IsClosedImmersion (i ∣_ O) := inferInstance
  set k : X ⟶ O.toScheme := inv (i ⁻¹ᵁ O).ι ≫ (i ∣_ O) with hkdef
  have hk : IsClosedImmersion k := inferInstance
  have hkpc : IsPseudoCoherentFromAfterPushforward k E m :=
    isPseudoCoherentFromAfterPushforward_precomp_inv_ι _ _ _ m
      (IsPseudoCoherentFromAfterPushforward.morphismRestrict i O E m h)
  have hkι : k ≫ O.ι = i := by
    rw [hkdef, Category.assoc, morphismRestrict_ι, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have hq : q.isoOpensRange.inv ≫ q = O.ι :=
    (Iso.inv_comp_eq _).2 (q.isoOpensRange_hom_ι).symm
  refine ⟨k ≫ q.isoOpensRange.inv, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hq, hkι]
  · rwa [isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff]

end Scheme.Modules

/-! ### The four moves on the condition of Stacks 09VC -/

/-- **Stacks 09VD at the base `⊤`.** Let `f : X ⟶ S` be a morphism of affine schemes locally of
finite type, let `i : X ⟶ 𝔸ⁿ_S` be a closed immersion over `S` along which the derived pushforward
of `E` is `m`-pseudo-coherent, and let `A` be an affine open of `X`. Then the same holds for
`E|_A` along some closed immersion of `A` into an affine space over `S` factoring `ι_A ≫ f`.

`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict` is Stacks 09VD
for a *standard* open `V` of the base and a morphism `X ⟶ V`; here `V = ⊤ = D(1)`, and `f` is
turned into a morphism to `(⊤ : S.Opens).toScheme` by composing with the canonical isomorphism
`AlgebraicGeometry.Scheme.topIso`, which moves the closed immersion along the induced isomorphism
of affine spaces. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_restrict_affineOpen
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    {n : ℕ} (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m) (A : X.affineOpens) :
    ∃ (k : ℕ) (j : (A.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = A.1.ι ≫ f ∧
          Scheme.Modules.IsPseudoCoherentFromAfterPushforward j
            ((Scheme.Modules.restrictFunctor A.1.ι).mapDerivedCategory.obj E) m := by
  have hVaff : IsAffine ((⊤ : S.Opens) : Scheme.{u}) := isAffineOpen_top S
  have hgι : (f ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι = f := by
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  have hft : LocallyOfFiniteType (f ≫ S.topIso.inv) := inferInstance
  have hqc : QuasiCompact (f ≫ S.topIso.inv) := inferInstance
  have hqover : AffineSpace.map (ULift.{u} (Fin n)) S.topIso.inv ≫
      (AffineSpace.over (ULift.{u} (Fin n)) ((⊤ : S.Opens) : Scheme.{u})).hom =
        (AffineSpace.over (ULift.{u} (Fin n)) S).hom ≫ S.topIso.inv := AffineSpace.map_over _
  obtain ⟨k, j, hj, hjo, hjpc⟩ := Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict
    (S := S) ⟨⊤, isAffineOpen_top S⟩ ⟨1, by simp⟩ (f ≫ S.topIso.inv) A E m
    ⟨n, i ≫ AffineSpace.map (ULift.{u} (Fin n)) S.topIso.inv, inferInstance,
      by rw [Category.assoc, hqover, ← Category.assoc, hi],
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff i
        (AffineSpace.map (ULift.{u} (Fin n)) S.topIso.inv) E m).2 h⟩
  refine ⟨k, j, hj, ?_, hjpc⟩
  rw [hjo]
  exact congrArg (fun t : X ⟶ S => A.1.ι ≫ t) hgι

/-- **Stacks 09VD along an open immersion of the source.** The same statement as
`AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_restrict_affineOpen`, for an open
immersion `a : X' ⟶ X` of affine schemes in place of the inclusion of an affine open.

`a` factors as the isomorphism `X' ≅ ι_a` of `AlgebraicGeometry.Scheme.Hom.isoOpensRange` followed
by the inclusion of its image, which is an affine open of `X`, so the affine-open case applies and
only the isomorphism has to be absorbed. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_openSource {X X' S : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (a : X' ⟶ X) [IsOpenImmersion a] {n : ℕ} (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    [IsClosedImmersion i] (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (k : ℕ) (j : X' ⟶ AffineSpace (ULift.{u} (Fin k)) S), IsClosedImmersion j ∧
      j ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = a ≫ f ∧
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward j
          ((Scheme.Modules.restrictFunctor a).mapDerivedCategory.obj E) m := by
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_restrict_affineOpen f i hi E m h
      ⟨a.opensRange, isAffineOpen_opensRange a⟩
  have := hl
  refine ⟨k, a.isoOpensRange.hom ≫ l, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hlo, ← Category.assoc, a.isoOpensRange_hom_ι]
  · rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_isIso_iff]
    exact Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso l hlpc
      (Scheme.Modules.derivedRestrictIsoOpensRangeIso a E).symm

/-- **Shrinking the base of the condition of Stacks 09VC along an open immersion.** Let
`i : X ⟶ 𝔸ⁿ_S` be a closed immersion along which the derived pushforward of `E` is
`m`-pseudo-coherent, and suppose the composite `X ⟶ 𝔸ⁿ_S ⟶ S` factors as `g ≫ b` for an open
immersion `b : W ⟶ S`. Then the same holds along a closed immersion of `X` into an affine space
over `W` factoring `g`.

`𝔸ⁿ_W` is the open subscheme `(𝔸ⁿ_S ↘ S)⁻¹W` of `𝔸ⁿ_S`
(`AlgebraicGeometry.opensRange_affineSpace_map`), which contains the image of `i` exactly because
`i ≫ (𝔸ⁿ_S ↘ S)` factors through `b`; so this is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_factor`, and the
factorisation lies over `W` because `b` is a monomorphism. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_shrinkBase {X S W : Scheme.{u}}
    (b : W ⟶ S) [IsOpenImmersion b] {n : ℕ} (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    [IsClosedImmersion i] (g : X ⟶ W)
    (hg : g ≫ b = i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ j : X ⟶ AffineSpace (ULift.{u} (Fin n)) W, IsClosedImmersion j ∧
      j ≫ (AffineSpace.over (ULift.{u} (Fin n)) W).hom = g ∧
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward j E m := by
  have hpre : i ⁻¹ᵁ (AffineSpace.map (ULift.{u} (Fin n)) b).opensRange = ⊤ := by
    rw [opensRange_affineSpace_map, ← Scheme.Hom.comp_preimage, ← hg,
      Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
    simp
  obtain ⟨j, hj, hjq, hjpc⟩ :=
    Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_factor i
      (AffineSpace.map (ULift.{u} (Fin n)) b) hpre E m h
  refine ⟨j, hj, ?_, hjpc⟩
  apply (cancel_mono b).1
  calc j ≫ (AffineSpace.over (ULift.{u} (Fin n)) W).hom ≫ b
      = j ≫ AffineSpace.map (ULift.{u} (Fin n)) b ≫
          (AffineSpace.over (ULift.{u} (Fin n)) S).hom :=
        congrArg (fun t : AffineSpace (ULift.{u} (Fin n)) W ⟶ S => j ≫ t)
          (AffineSpace.map_over b).symm
    _ = i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom := by rw [← Category.assoc, hjq]
    _ = g ≫ b := hg.symm

/-- **Stacks 09VD at the affine open `⊤` of the source.** Let `S` be affine, let `V` be an affine
open of `S` which is a standard open, let `X` be affine and `g : X ⟶ V` locally of finite type,
and let `i : X ⟶ 𝔸ⁿ_V` be a closed immersion over `V` along which the derived pushforward of `E`
is `m`-pseudo-coherent. Then the same holds along a closed immersion of `X` into an affine space
over `S` factoring `g ≫ ι_V`.

`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict` is applied at the
affine open `⊤` of `X`, and the closed immersion it produces is moved back from
`(⊤ : X.Opens).toScheme` to `X` by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_inv_ι`. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_basicOpenBase {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (V : S.affineOpens) (hV : ∃ a : Γ(S, ⊤), V.1 = S.basicOpen a)
    (g : X ⟶ (V.1 : Scheme.{u})) [LocallyOfFiniteType g] {n : ℕ}
    (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = g)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (k : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin k)) S), IsClosedImmersion j ∧
      j ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = g ≫ V.1.ι ∧
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward j E m := by
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hqc : QuasiCompact g := inferInstance
  have hAiso : IsIso (⊤ : X.Opens).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Scheme.Opens.opensRange_ι ⊤)
  obtain ⟨k, l, hl, hlo, hlpc⟩ := Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict
    V hV g ⟨⊤, isAffineOpen_top X⟩ E m ⟨n, i, ‹IsClosedImmersion i›, hi, h⟩
  have := hl
  refine ⟨k, inv (⊤ : X.Opens).ι ≫ l, inferInstance, ?_,
    Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_inv_ι ⊤ l E m hlpc⟩
  rw [Category.assoc, hlo, ← Category.assoc, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]


/-! ### Refining a cover of an affine scheme by finitely many standard opens -/

/-- An open cover of an affine scheme is refined by a *finite* family of standard opens: each
point lies in a standard open inside some member of the cover
(`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`), and the space is quasi-compact. The
conclusion is phrased with `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`, which is the form
Stacks 09VE consumes. -/
public theorem exists_fin_basicOpen_refinement {X : Scheme.{u}} [IsAffine X] {ι : Type*}
    (O : ι → X.Opens) (hO : (⨆ i, O i) = ⊤) :
    ∃ (N : ℕ) (g : Fin N → Γ(X, ⊤)) (a : Fin N → ι),
      PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ∧ ∀ j, X.basicOpen (g j) ≤ O (a j) := by
  classical
  have hcover : (Set.univ : Set X) ⊆
      ⋃ b : {b : Γ(X, ⊤) × ι // X.basicOpen b.1 ≤ O b.2}, (X.basicOpen b.1.1).1 := by
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hO ▸ (Opens.mem_top x))
    obtain ⟨b, hbO, hxb⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := O i) ⟨x, hi⟩ trivial
    exact Set.mem_iUnion.2 ⟨⟨(b, i), hbO⟩, hxb⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : {b : Γ(X, ⊤) × ι // X.basicOpen b.1 ≤ O b.2} => (X.basicOpen b.1.1).1)
    (fun b => (X.basicOpen b.1.1).2) hcover
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1.1, fun j => (t.equivFin.symm j).1.1.2,
    (Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr ?_,
    fun j => (t.equivFin.symm j).1.2⟩
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨b, hb, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨b, hb⟩, by simpa using hx⟩

/-! ### Factoring a morphism through an open subscheme of its target -/

/-- A morphism of schemes all of whose image lies in an open subscheme `V` of its target,
factored through `V`. -/
public def Scheme.Hom.liftOpens {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (h : ∀ x : X, f.base x ∈ V) : X ⟶ (V : Scheme.{u}) :=
  IsOpenImmersion.lift V.ι f (by rintro _ ⟨x, rfl⟩; exact ⟨⟨f.base x, h x⟩, rfl⟩)

/-- `AlgebraicGeometry.Scheme.Hom.liftOpens` followed by the inclusion of the open subscheme is
the original morphism. -/
@[reassoc (attr := simp)]
public theorem Scheme.Hom.liftOpens_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (h : ∀ x : X, f.base x ∈ V) : f.liftOpens V h ≫ V.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- An open immersion factored through an open subscheme of its target is again an open
immersion, because composing it with the inclusion gives back the open immersion. -/
public theorem Scheme.Hom.isOpenImmersion_liftOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (V : Y.Opens) (h : ∀ x : X, f.base x ∈ V) :
    IsOpenImmersion (f.liftOpens V h) := by
  have : IsOpenImmersion (f.liftOpens V h ≫ V.ι) := by
    rw [Scheme.Hom.liftOpens_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ V.ι

/-- Two ways of restricting `E` twice along a commuting square of open immersions give objects
related by an isomorphism, so the local condition at `j` transfers from one to the other. -/
private theorem isPseudoCoherentFromAfterPushforward_restrict_restrict_of_comm
    {X P U B Y : Scheme.{u}} (a : B ⟶ P) (p : P ⟶ X) (b : B ⟶ U) (u : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion p] [IsOpenImmersion b] [IsOpenImmersion u]
    (h : a ≫ p = b ≫ u) (j : B ⟶ Y) [IsClosedImmersion j] (E : DerivedCategory X.Modules) (m : ℤ)
    (hj : Scheme.Modules.IsPseudoCoherentFromAfterPushforward j
      ((Scheme.Modules.restrictFunctor a).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor p).mapDerivedCategory.obj E)) m) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward j
      ((Scheme.Modules.restrictFunctor b).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor u).mapDerivedCategory.obj E)) m := by
  refine Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso j hj ?_
  exact (Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorComp a p).symm).app E ≪≫
    (Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorCongr h)).app E ≪≫
    (Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorComp b u).symm).symm.app E

/-! ### Stacks 09UJ -/

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The local step of Stacks 09UJ.** Suppose the local condition of Stacks 09UI holds at a
compatible pair of affine opens `P ⊆ f ⁻¹ᵁ T`, let `U ⊆ f ⁻¹ᵁ V` be another compatible pair of
affine opens, let `D(r) ⊆ V` be a standard open of `V` contained in `ι_V⁻¹T`, and let `B` be an
affine open of `U` inside `ι_U⁻¹P ∩ (f|_U)⁻¹D(r)`. Then the local condition holds for
`B ⟶ V` and the restriction of `E` to `B`.

The three moves of this file are applied in turn: `B ⟶ P` is an open immersion of affine schemes,
so the condition passes from `P ⟶ T` to `B ⟶ T`; the composite `B ⟶ T` factors through the open
immersion `D(r) ⟶ T`, so it passes to `B ⟶ D(r)`; and `D(r)` is a standard open of `V`, so it
passes to `B ⟶ V`. -/
public theorem isPseudoCoherentFromAfterPushforward_overlap [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) (P U : X.affineOpens) (T V : S.affineOpens)
    (hPT : P.1 ≤ f ⁻¹ᵁ T.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hP : f.IsPseudoCoherentFromOnAffinePair E m P T hPT)
    (r : Γ((V.1 : Scheme.{u}), ⊤)) (hr : (V.1 : Scheme.{u}).basicOpen r ≤ V.1.ι ⁻¹ᵁ T.1)
    (B : (U.1 : Scheme.{u}).affineOpens)
    (hB : B.1 ≤ (U.1.ι ⁻¹ᵁ P.1) ⊓ (f.resLE V.1 U.1 hUV ⁻¹ᵁ (V.1 : Scheme.{u}).basicOpen r)) :
    ∃ (k : ℕ) (j : (B.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin k)) (V.1 : Scheme.{u})),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin k)) (V.1 : Scheme.{u})).hom =
          B.1.ι ≫ f.resLE V.1 U.1 hUV ∧
          Scheme.Modules.IsPseudoCoherentFromAfterPushforward j
            ((Scheme.Modules.restrictFunctor B.1.ι).mapDerivedCategory.obj
              ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E)) m := by
  obtain ⟨n, i, hi, hio, hipc⟩ := hP
  have := hi
  have hPaff : IsAffine (P.1 : Scheme.{u}) := P.2
  have hTaff : IsAffine (T.1 : Scheme.{u}) := T.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hBaff : IsAffine (B.1 : Scheme.{u}) := B.2
  have hWaffOpen : IsAffineOpen ((V.1 : Scheme.{u}).basicOpen r) :=
    (isAffineOpen_top (V.1 : Scheme.{u})).basicOpen r
  have hWaff : IsAffine (((V.1 : Scheme.{u}).basicOpen r : (V.1 : Scheme.{u}).Opens) :
    Scheme.{u}) := hWaffOpen
  set a : (B.1 : Scheme.{u}) ⟶ (P.1 : Scheme.{u}) :=
    (B.1.ι ≫ U.1.ι).liftOpens P.1 (fun x => (hB x.2).1)
  set b : (((V.1 : Scheme.{u}).basicOpen r : (V.1 : Scheme.{u}).Opens) : Scheme.{u}) ⟶
      (T.1 : Scheme.{u}) :=
    (((V.1 : Scheme.{u}).basicOpen r).ι ≫ V.1.ι).liftOpens T.1 (fun x => hr x.2)
  set g : (B.1 : Scheme.{u}) ⟶
      (((V.1 : Scheme.{u}).basicOpen r : (V.1 : Scheme.{u}).Opens) : Scheme.{u}) :=
    (B.1.ι ≫ f.resLE V.1 U.1 hUV).liftOpens ((V.1 : Scheme.{u}).basicOpen r)
      (fun x => (hB x.2).2)
  have haι : a ≫ P.1.ι = B.1.ι ≫ U.1.ι := Scheme.Hom.liftOpens_ι _ _ _
  have hbι : b ≫ T.1.ι = ((V.1 : Scheme.{u}).basicOpen r).ι ≫ V.1.ι :=
    Scheme.Hom.liftOpens_ι _ _ _
  have hgι : g ≫ ((V.1 : Scheme.{u}).basicOpen r).ι = B.1.ι ≫ f.resLE V.1 U.1 hUV :=
    Scheme.Hom.liftOpens_ι _ _ _
  have hao : IsOpenImmersion a := Scheme.Hom.isOpenImmersion_liftOpens _ _ _
  have hbo : IsOpenImmersion b := Scheme.Hom.isOpenImmersion_liftOpens _ _ _
  have e1 : (g ≫ b) ≫ T.1.ι = (B.1.ι ≫ U.1.ι) ≫ f := by
    rw [Category.assoc, hbι, ← Category.assoc, hgι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc]
  have e2 : (a ≫ f.resLE T.1 P.1 hPT) ≫ T.1.ι = (B.1.ι ≫ U.1.ι) ≫ f := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, haι]
  have hcomm : g ≫ b = a ≫ f.resLE T.1 P.1 hPT :=
    (cancel_mono T.1.ι).1 (e1.trans e2.symm)
  obtain ⟨k₁, j₁, hj₁, hj₁o, hj₁pc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_openSource (f.resLE T.1 P.1 hPT) a i hio _ m hipc
  have := hj₁
  obtain ⟨j₂, hj₂, hj₂o, hj₂pc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_shrinkBase b j₁ g (by rw [hcomm, hj₁o]) _ m hj₁pc
  have := hj₂
  have hgft : LocallyOfFiniteType g := by
    rw [← hj₂o]
    exact MorphismProperty.comp_mem _ _ _ inferInstance (by
      rw [AffineSpace.over_hom_eq]
      infer_instance)
  obtain ⟨k₃, j₃, hj₃, hj₃o, hj₃pc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpenBase
      ⟨(V.1 : Scheme.{u}).basicOpen r, hWaffOpen⟩ ⟨r, rfl⟩ g j₂ hj₂o _ m hj₂pc
  refine ⟨k₃, j₃, hj₃, by rw [hj₃o, hgι], ?_⟩
  exact isPseudoCoherentFromAfterPushforward_restrict_restrict_of_comm a P.1.ι B.1.ι U.1.ι haι j₃
    E m hj₃pc

/-- **Stacks 09UJ.** For `f : X ⟶ S` locally of finite type, `E` an object of the derived
category of `𝒪_X`-modules and `m` an integer, `E` is relatively `m`-pseudo-coherent if and only
if the local condition of Stacks 09UI holds at every compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`.

The two implications are
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair` and
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom`. -/
@[stacks 09UJ "affine-open characterization"]
public theorem isPseudoCoherentFrom_iff_forall_affinePair [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) : AffinePairComparison f E m :=
  ⟨fun hE => isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE,
    isPseudoCoherentFrom_of_forall_affinePair f E m⟩

/-- The local condition of Stacks 09UI at a compatible pair of affine opens holds at *every*
closed immersion of `U` into an affine space over `V` factoring `f|_U`, not just at the one it
asserts the existence of. This is the equivalence of Stacks 09VC
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin`), and it is what lets
two objects with separately chosen witnesses be compared at one common closed immersion. -/
public theorem IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion [LocallyOfFiniteType f]
    {E : DerivedCategory X.Modules} {m : ℤ} {U : X.affineOpens} {V : S.affineOpens}
    {hUV : U.1 ≤ f ⁻¹ᵁ V.1} (h : f.IsPseudoCoherentFromOnAffinePair E m U V hUV) (n : ℕ)
    (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}))
    (hi : IsClosedImmersion i)
    (hio : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom =
      f.resLE V.1 U.1 hUV) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward i
      ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E) m :=
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  (Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin (f.resLE V.1 U.1 hUV) _ m).1 h n i
    hi hio

/-- **Stacks 09UJ, the final assertion.** If `E` is `m`-pseudo-coherent relative to `S`, then for
every pair of open subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V` the restriction `E|_U` is
`m`-pseudo-coherent relative to `V`.

By `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair` it is enough to
check the local condition at a compatible pair of affine opens `A ⊆ U`, `B ⊆ V`; their images in
`X` and `S` are a compatible pair of affine opens there, the same lemma supplies the condition at
that pair, and the two canonical isomorphisms `A ≅ ι_U(A)` and `B ≅ ι_V(B)` are absorbed by
`AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_openSource` and
`AlgebraicGeometry.exists_isPseudoCoherentFromAfterPushforward_shrinkBase`. -/
@[stacks 09UJ "restriction to open subschemes", sga "6 III 1.1" "(i)"]
public theorem IsPseudoCoherentFrom.resLE [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (hE : IsPseudoCoherentFrom f E m) :
    IsPseudoCoherentFrom (f.resLE V U hUV)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) m := by
  refine isPseudoCoherentFrom_of_forall_affinePair _ _ m fun A B hAB => ?_
  set A' : X.affineOpens := ⟨U.ι ''ᵁ A.1, A.2.image_of_isOpenImmersion U.ι⟩
  set B' : S.affineOpens := ⟨V.ι ''ᵁ B.1, B.2.image_of_isOpenImmersion V.ι⟩
  have hA'aff : IsAffine (A'.1 : Scheme.{u}) := A'.2
  have hB'aff : IsAffine (B'.1 : Scheme.{u}) := B'.2
  have hAaff : IsAffine (A.1 : Scheme.{u}) := A.2
  have haι : (U.ι.isoImage A.1).hom ≫ A'.1.ι = A.1.ι ≫ U.ι := U.ι.isoImage_hom_ι A.1
  have hbι : (V.ι.isoImage B.1).hom ≫ B'.1.ι = B.1.ι ≫ V.ι := V.ι.isoImage_hom_ι B.1
  have hA'B' : A'.1 ≤ f ⁻¹ᵁ B'.1 := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨(f.resLE V U hUV).base y, hAB hy,
      congrArg (fun k : (U : Scheme.{u}) ⟶ S => k.base y) (Scheme.Hom.resLE_comp_ι f hUV)⟩
  obtain ⟨n, i, hi, hio, hipc⟩ :=
    isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE A' B' hA'B'
  have := hi
  have e1 : ((U.ι.isoImage A.1).hom ≫ f.resLE B'.1 A'.1 hA'B') ≫ B'.1.ι =
      (A.1.ι ≫ U.ι) ≫ f := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, haι]
  have e2 : (((f.resLE V U hUV).resLE B.1 A.1 hAB) ≫ (V.ι.isoImage B.1).hom) ≫ B'.1.ι =
      (A.1.ι ≫ U.ι) ≫ f := by
    rw [Category.assoc, hbι, Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc]
  obtain ⟨k₁, j₁, hj₁, hj₁o, hj₁pc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_openSource (f.resLE B'.1 A'.1 hA'B')
      (U.ι.isoImage A.1).hom i hio _ m hipc
  have := hj₁
  have hcomm : (f.resLE V U hUV).resLE B.1 A.1 hAB ≫ (V.ι.isoImage B.1).hom =
      j₁ ≫ (AffineSpace.over (ULift.{u} (Fin k₁)) (B'.1 : Scheme.{u})).hom := by
    rw [hj₁o]
    exact (cancel_mono B'.1.ι).1 (e2.trans e1.symm)
  obtain ⟨j₂, hj₂, hj₂o, hj₂pc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_shrinkBase (V.ι.isoImage B.1).hom j₁
      ((f.resLE V U hUV).resLE B.1 A.1 hAB) hcomm _ m hj₁pc
  refine ⟨k₁, j₂, hj₂, hj₂o, ?_⟩
  exact isPseudoCoherentFromAfterPushforward_restrict_restrict_of_comm (U.ι.isoImage A.1).hom
    A'.1.ι A.1.ι U.ι haι j₂ E m hj₂pc

end Scheme.Hom

end AlgebraicGeometry

end
