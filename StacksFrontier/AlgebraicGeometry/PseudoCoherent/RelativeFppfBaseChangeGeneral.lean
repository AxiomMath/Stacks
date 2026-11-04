module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ChartTorIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Relative `m`-pseudo-coherence along an fppf covering of an arbitrary base

Let `f : X ⟶ S` be locally of finite type, let `{g a : S a ⟶ S}` be an fppf covering, write
`X a = X ×_S S a` and let `f a : X a ⟶ S a` and `p a : X a ⟶ X` be the two projections. For an
object `E` of `D(𝒪_X)` and an integer `m`, Stacks 0CSQ says that `E` is `m`-pseudo-coherent
relative to `S` if and only if every `L(p a)^*E` is `m`-pseudo-coherent relative to `S a`.

Both directions are proved here, for `f` locally of finite type over an arbitrary base and for an
arbitrary object of `D(𝒪_X)`. The module
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfBaseChange` proves the same equivalence
for a pseudo-coherent `f`, and for `f` locally of finite type over a locally Noetherian base; both
are special cases of `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_pullback_snd`.

The forward direction is Stacks 09UR: a member of an fppf covering is flat, and a flat morphism is
Tor independent from every morphism to the same target, so the base change of the hypothesis is
immediate.

For the converse the covering is pushed into the charts that define relative pseudo-coherence. By
Stacks 09UJ it suffices to produce, at each pair of affine opens `U ⊆ f⁻¹(V)` of `X` and `S` and
one closed immersion `i : U ⟶ 𝔸ⁿ_V` over `V` factoring `f|_U`, absolute `m`-pseudo-coherence of
`Ri_*(E|_U)` on `𝔸ⁿ_V`. Now `𝔸ⁿ_V` carries an fppf covering of its own: for every `a` and every
affine open `V' ⊆ (g a)⁻¹(V)` of `S a`, the morphism `𝔸ⁿ_{V'} ⟶ 𝔸ⁿ_V` is the base change of
`V' ⟶ V` along `𝔸ⁿ_V ⟶ V`, and those `V' ⟶ V` jointly cover `V`. Each member is a flat morphism
locally of finite presentation, so Stacks 09UF — absolute fppf descent of `m`-pseudo-coherence —
reduces the claim to the derived pullback of `Ri_*(E|_U)` to each `𝔸ⁿ_{V'}`. That pullback is
`Re_*(L(p a)^*E|_W)` for the base-changed chart `e : W ⟶ 𝔸ⁿ_{V'}` of
`AlgebraicGeometry.exists_isClosedImmersion_baseChange_affineSpace`, by Stacks 0E23 at the
cartesian square of `e` over `i`, whose horizontal morphism is flat; and that is the chart
condition for `L(p a)^*E` at the affine pair `W ⊆ (f a)⁻¹(V')`, which the hypothesis supplies.

## Main results

In `AlgebraicGeometry.Scheme.Hom`:

* `isPseudoCoherentFrom_of_forall_pullback_snd`: the descent direction of Stacks 0CSQ.
* `isPseudoCoherentFrom_iff_forall_pullback_snd`: **Stacks 0CSQ**, both directions.

## Implementation notes

**Why the chart route works here.** The analogous statement for an arbitrary fppf covering of `X`
is Stacks 0CSN, and there this argument is unavailable: a general covering of `X` induces no
covering of the ambient affine space of a chart, which is why the source descends along a
surjective finite locally free morphism instead and has to assume that the cohomology sheaves of
`E` are quasi-coherent. Here the covering of `X` is the base change of a covering of `S`, so it
*does* induce one on `𝔸ⁿ_V`, and the absolute descent of Stacks 09UF — which holds for an
arbitrary object of `D(𝒪_X)` — is enough.

**No hypothesis on the cohomology sheaves of `E`.** The source assumes `E` in `D_QCoh(𝒪_X)`. That
hypothesis is not used on this route, so the statements below quantify over all of `D(𝒪_X)`.

**The index type of the covering.** A family in `AlgebraicGeometry.Scheme.fppfPrecoverage` is a
`CategoryTheory.Presieve.ofArrows`, whose index type may live in any universe; it is kept free.
The covering of `𝔸ⁿ_V` built from it is indexed by pairs of a member of the covering and an affine
open of that member lying over `V`, so its index type lives in the maximum of the two universes,
which is what `CategoryTheory.Precoverage.mem_coverings_of_isPullback` allows.

**The instances on the two projections.** `f a` is locally of finite type because `f` is and that
property is stable under base change, so the right-hand side needs no instance beyond the binders;
flatness of `g a`, which the forward direction and the covering of `𝔸ⁿ_V` both use, is read off
the covering.

Flatness and local finite presentation of the restriction `V' ⟶ V` of a member `g a` are obtained
from `AlgebraicGeometry.IsZariskiLocalAtSource.resLE`; the two localness instances for each of the
two properties are named from `AlgebraicGeometry.HasRingHomProperty`, as
`AlgebraicGeometry.locallyOfFiniteType_resLE` does for local finite type.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
made a local instance at a high priority because part of the import closure supplies a global
instance of the same class; this is the declaration made by Stacks 09UI, 09UF, 09UJ and 09UR, in
whose spelling the statements below are read.

## Where Stacks 0CSL is

Stacks 0CSL is the global-sections criterion for the very predicate this file is about: for
`f : X ⟶ Spec A` separated and of finite presentation and `K` in `D_QCoh(𝒪_X)`, `K` is
pseudo-coherent relative to the base as soon as `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent over `A` for
every absolutely pseudo-coherent `E` on `X`. Its conclusion is exactly
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`, which is why the state of the tag is
recorded here.

The source's proof is formalized as
`AlgebraicGeometry.isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPseudoCoherent`, through
Stacks 0CSJ, Stacks 0CSK, Stacks 0CSD, Stacks 0CSG, Stacks 09UU, the projection formula of Stacks
08EU and the locality of relative pseudo-coherence on the source.

## References

* [The Stacks Project, Lemma 37.70.3 (0CSQ)](https://stacks.math.columbia.edu/tag/0CSQ)
* [The Stacks Project, Lemma 37.70.1 (0CSN)](https://stacks.math.columbia.edu/tag/0CSN)
* [The Stacks Project, Lemma 36.12.3 (09UF)](https://stacks.math.columbia.edu/tag/09UF)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 37.59.15 (09UR)](https://stacks.math.columbia.edu/tag/09UR)
* [The Stacks Project, Lemma 36.22.9 (0E23)](https://stacks.math.columbia.edu/tag/0E23)
* [The Stacks Project, Definition 37.59.2 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.PseudoCoherence.FlatDescent
  (exists_preimage_of_mem_fppfPrecoverage flat_of_mem_fppfPrecoverage
    locallyOfFinitePresentation_of_mem_fppfPrecoverage isPseudoCoherentFrom_iff_forall_fppf)

namespace AlgebraicGeometry

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

/-- The index type of the covering of an affine space over an affine open `V` of `S` induced by an
fppf covering `{g a}` of `S`: a member of the covering together with an affine open of it lying
over `V`. -/
private abbrev FppfChartIndex {S : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (g : ∀ a, Y a ⟶ S) (V : S.affineOpens) : Type max v u :=
  Σ a : ι, {V' : (Y a).affineOpens // V'.1 ≤ g a ⁻¹ᵁ V.1}

/-- **An fppf covering of the base induces one on an affine space over an affine open of it.**
Let `{g a : Y a ⟶ S}` be an fppf covering and let `V` be an affine open of `S`. The morphisms
`𝔸ᴺ_{V'} ⟶ 𝔸ᴺ_V` induced by the restrictions `V' ⟶ V` of the members, for `V'` an affine open of
some `Y a` contained in `(g a)⁻¹(V)`, form an fppf covering of `𝔸ᴺ_V`.

The restrictions `V' ⟶ V` jointly cover `V`, because the members of the covering do and every
point of a scheme has an affine open neighbourhood inside a given open; each is flat and locally
of finite presentation because those properties are Zariski local at the source and at the
target. Affine space over `V'` is the fibre product of `𝔸ᴺ_V` and `V'` over `V`, so the induced
family is a base change of that covering. -/
private theorem ofArrows_affineSpaceMap_mem_fppfPrecoverage {S : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (g : ∀ a, Y a ⟶ S)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S) (V : S.affineOpens) (N : Type u) :
    Presieve.ofArrows
        (fun j : FppfChartIndex Y g V => 𝔸(N; (j.2.1.1 : Scheme.{u})))
        (fun j => AffineSpace.map N ((g j.1).resLE V.1 j.2.1.1 j.2.2)) ∈
      Scheme.fppfPrecoverage 𝔸(N; (V.1 : Scheme.{u})) := by
  let : IsZariskiLocalAtSource (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Flat)
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  have hsurj : ∀ x : (V.1 : Scheme.{u}), ∃ j : FppfChartIndex Y g V,
      x ∈ Set.range ((g j.1).resLE V.1 j.2.1.1 j.2.2) := by
    intro x
    obtain ⟨a, y, hy⟩ := exists_preimage_of_mem_fppfPrecoverage Y g hg (V.1.ι x)
    have hyV : y ∈ g a ⁻¹ᵁ V.1 := by
      change (g a).base y ∈ V.1
      rw [hy]
      exact x.2
    obtain ⟨W, hW, hyW, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y a) (x := y) (U := g a ⁻¹ᵁ V.1) hyV
    exact ⟨⟨a, ⟨⟨W, hW⟩, hWsub⟩⟩, ⟨y, hyW⟩,
      Subtype.ext (((g a).coe_resLE_apply hWsub ⟨y, hyW⟩).trans hy)⟩
  have hcovV : Presieve.ofArrows (fun j : FppfChartIndex Y g V => (j.2.1.1 : Scheme.{u}))
      (fun j => (g j.1).resLE V.1 j.2.1.1 j.2.2) ∈
        Scheme.fppfPrecoverage (V.1 : Scheme.{u}) := by
    rw [Scheme.fppfPrecoverage_eq_inf]
    refine ⟨(Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mpr ⟨hsurj, fun j => ?_⟩,
      (Scheme.ofArrows_mem_precoverage_iff
        (P := @LocallyOfFinitePresentation)).mpr ⟨hsurj, fun j => ?_⟩⟩
    · exact IsZariskiLocalAtSource.resLE _ (flat_of_mem_fppfPrecoverage Y g hg j.1)
    · exact IsZariskiLocalAtSource.resLE _
        (locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg j.1)
  exact Precoverage.mem_coverings_of_isPullback
    (fun j : FppfChartIndex Y g V => (g j.1).resLE V.1 j.2.1.1 j.2.2) hcovV
    (𝔸(N; (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u})) _ _
    fun j => AffineSpace.isPullback_map (n := N) _

/-- The local condition of Stacks 09UI at a closed immersion `i` is absolute `m`-pseudo-coherence
of the derived pushforward along `i`. -/
private theorem isPseudoCoherentFromAfterPushforward_iff_derivedPushforward {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward i E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((derivedPushforward i.toLRSHom.toShHom).obj E) m := by
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i E m]
  exact ⟨fun h => h.of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E).symm,
    fun h => h.of_iso
      ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app E)⟩

/-- **Absolute `m`-pseudo-coherence of a derived pushforward is reflected by an invertible base
change map.** Let

```
W --e--> P'
|wU       |q
U --i--> P
```

be a commutative square with `i` and `e` closed immersions, let `F` be an object of `D(𝒪_U)` and
suppose the canonical derived base change map is invertible at `F`. If the derived pushforward
along `e` of `Lw_U^*F` satisfies the local condition of Stacks 09UI, then the derived pullback
along `q` of `Ri_*F` is `m`-pseudo-coherent on `P'`.

This is the reverse reading of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_baseChange`: that local
condition is absolute `m`-pseudo-coherence of `Re_*(Lw_U^*F)` by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`, and the base change
map identifies it with `Lq^*(Ri_*F)`. -/
private theorem isPseudoCoherentFrom_derivedPullback_derivedPushforward_of_baseChange
    {U W P P' : Scheme.{u}} (i : U ⟶ P) (e : W ⟶ P') (wU : W ⟶ U) (q : P' ⟶ P)
    [IsClosedImmersion i] [IsClosedImmersion e] (F : DerivedCategory U.Modules) (m : ℤ)
    (hsq : wU.toLRSHom.toShHom ≫ i.toLRSHom.toShHom =
      e.toLRSHom.toShHom ≫ q.toLRSHom.toShHom)
    (hBC : IsIso (derivedBaseChangeMap wU.toLRSHom.toShHom e.toLRSHom.toShHom
      i.toLRSHom.toShHom q.toLRSHom.toShHom hsq F))
    (hW : Scheme.Modules.IsPseudoCoherentFromAfterPushforward e
      ((derivedPullback wU.toLRSHom.toShHom).obj F) m) :
    RingedSpace.IsPseudoCoherentFrom (X := P'.toRingedSpace)
      ((derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj F)) m := by
  have := hBC
  exact ((isPseudoCoherentFromAfterPushforward_iff_derivedPushforward e _ m).mp hW).of_iso
    (asIso (derivedBaseChangeMap wU.toLRSHom.toShHom e.toLRSHom.toShHom
      i.toLRSHom.toShHom q.toLRSHom.toShHom hsq F)).symm

/-- **The descent direction of Stacks 0CSQ at one chart and one member of the covering.** Let
`f : X ⟶ S` be locally of finite type, let `g : S' ⟶ S` be flat, and suppose the derived pullback
of `E` to `X ×_S S'` is `m`-pseudo-coherent relative to `S'`. For affine opens `V` of `S`,
`V' ⊆ g⁻¹(V)` of `S'` and `U ⊆ f⁻¹(V)` of `X` and a closed immersion `i : U ⟶ 𝔸ⁿ_V` over `V`
factoring `f|_U`, the derived pullback of `Ri_*(E|_U)` to `𝔸ⁿ_{V'}` is `m`-pseudo-coherent.

The chart `e : W ⟶ 𝔸ⁿ_{V'}` base changed from `i` sits in a cartesian square over `i` whose
horizontal morphism `𝔸ⁿ_{V'} ⟶ 𝔸ⁿ_V` is flat, so Stacks 0E23 applies to it; the local condition
at `e` is the hypothesis read at the affine pair `W ⊆ (pullback.snd f g)⁻¹(V')` through
Stacks 09UJ and 09VC. -/
private theorem isPseudoCoherentFrom_derivedPullback_derivedPushforward_chart
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] [Flat g]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hE : (pullback.snd f g).IsPseudoCoherentFrom
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj E) m)
    (V : S.affineOpens) (V' : S'.affineOpens) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (n : ℕ)
    (i : (U.1 : Scheme.{u}) ⟶ 𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u})))
    (hi : IsClosedImmersion i)
    (hio : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom =
      f.resLE V.1 U.1 hUV) :
    RingedSpace.IsPseudoCoherentFrom
      (X := (𝔸(ULift.{u} (Fin n); (V'.1 : Scheme.{u}))).toRingedSpace)
      ((derivedPullback (AffineSpace.map (ULift.{u} (Fin n))
            (g.resLE V.1 V'.1 hV')).toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj
          ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E))) m := by
  have := hi
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  have : IsAffine (V'.1 : Scheme.{u}) := V'.2
  obtain ⟨e, he, hebase, hSq⟩ :=
    exists_isClosedImmersion_baseChange_affineSpace f g hUV hV' (ULift.{u} (Fin n)) i hio
  have := he
  have hpair := Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom
    (pullback.snd f g) hE
    ⟨pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1,
      isAffineOpen_inf_preimage f g hUV hV'⟩ V' inf_le_right
  have hafter := Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion
    (pullback.snd f g) hpair n e he hebase
  have hres : Scheme.Modules.IsPseudoCoherentFromAfterPushforward e
      ((derivedPullback ((pullback.fst f g).resLE U.1 _ inf_le_left).toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E)) m :=
    hafter.of_iso e (Scheme.Modules.openRestrictionDerivedPullbackIso
      (pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V'.1 : (pullback f g).Opens).ι
      (pullback.fst f g) U.1.ι ((pullback.fst f g).resLE U.1 _ inf_le_left)
      (Scheme.Hom.resLE_comp_ι (pullback.fst f g) inf_le_left).symm E)
  exact isPseudoCoherentFrom_derivedPullback_derivedPushforward_of_baseChange i e
    ((pullback.fst f g).resLE U.1 _ inf_le_left)
    (AffineSpace.map (ULift.{u} (Fin n)) (g.resLE V.1 V'.1 hV')) _ m
    (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback hSq.flip)
    (derivedBaseChangeIsoOfTorIndependent hSq.flip hi
      (f.chartTorIndependence_of_torIndependent g (torIndependent_of_flat_right f g)
        V V' hV' U hUV n i hi hio) _)
    hres

/-- **Stacks 0CSQ, the descent direction.** Let `f : X ⟶ S` be locally of finite type, let
`{g a : Y a ⟶ S}` be an fppf covering, let `E` be an object of `D(𝒪_X)` and let `m` be an integer.
If the derived pullback of `E` to `X ×_S Y a` is `m`-pseudo-coherent relative to `Y a` for every
`a`, then `E` is `m`-pseudo-coherent relative to `S`.

By Stacks 09UJ it is enough to exhibit, at every pair of affine opens `U ⊆ f⁻¹(V)`, one closed
immersion of `U` into an affine space over `V` at which the local condition of Stacks 09UI holds;
the one supplied by `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE` is used. The
condition there is absolute `m`-pseudo-coherence of the derived pushforward, which descends along
the fppf covering of that affine space induced by `{g a}` by Stacks 09UF. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_forall_pullback_snd {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ a, Y a ⟶ S)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S) (E : DerivedCategory X.Modules)
    (m : ℤ)
    (h : ∀ a, (pullback.snd f (g a)).IsPseudoCoherentFrom
      ((derivedPullback (pullback.fst f (g a)).toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  refine Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair f E m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  have := hi
  refine ⟨n, i, hi, hio, ?_⟩
  have habs : RingedSpace.IsPseudoCoherentFrom
      (X := (𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u}))).toRingedSpace)
      ((derivedPushforward i.toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E)) m := by
    refine (isPseudoCoherentFrom_iff_forall_fppf
      (fun j : FppfChartIndex Y g V => 𝔸(ULift.{u} (Fin n); (j.2.1.1 : Scheme.{u})))
      (fun j => AffineSpace.map (ULift.{u} (Fin n)) ((g j.1).resLE V.1 j.2.1.1 j.2.2))
      (ofArrows_affineSpaceMap_mem_fppfPrecoverage Y g hg V (ULift.{u} (Fin n)))
      ((derivedPushforward i.toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E)) m).mpr fun j => ?_
    have : Flat (g j.1) := flat_of_mem_fppfPrecoverage Y g hg j.1
    exact isPseudoCoherentFrom_derivedPullback_derivedPushforward_chart f (g j.1) E m (h j.1)
      V j.2.1 j.2.2 U hUV n i hi hio
  exact (isPseudoCoherentFromAfterPushforward_iff_derivedPushforward i _ m).mpr habs

/-- **Stacks 0CSQ.** Let `f : X ⟶ S` be locally of finite type, let `{g a : Y a ⟶ S}` be an fppf
covering, let `E` be an object of `D(𝒪_X)` and let `m` be an integer. Then `E` is
`m`-pseudo-coherent relative to `S` if and only if the derived pullback of `E` to `X ×_S Y a` is
`m`-pseudo-coherent relative to `Y a` for every `a`.

The forward direction is Stacks 09UR at the flat morphism `g a`; the converse is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_pullback_snd`. No hypothesis on the
cohomology sheaves of `E` is used. -/
@[stacks 0CSQ]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_forall_pullback_snd {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ a, Y a ⟶ S)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S) (E : DerivedCategory X.Modules)
    (m : ℤ) :
    f.IsPseudoCoherentFrom E m ↔
      ∀ a, (pullback.snd f (g a)).IsPseudoCoherentFrom
        ((derivedPullback (pullback.fst f (g a)).toLRSHom.toShHom).obj E) m :=
  ⟨fun hE a =>
    have : Flat (g a) := flat_of_mem_fppfPrecoverage Y g hg a
    Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_torIndependent f (g a) E m
      (torIndependent_of_flat_right f (g a)) hE,
    Scheme.Hom.isPseudoCoherentFrom_of_forall_pullback_snd f Y g hg E m⟩

end AlgebraicGeometry

end
