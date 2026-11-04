module

public import Mathlib.RingTheory.Etale.Locus
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleSmoothUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentEtale
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocal
import StacksCore.Tactic.StacksAttribute

/-!
# Formal étaleness read on the naive cotangent complex

[Stacks Project, Tag 0D0M] says that a morphism of schemes `f : X ⟶ S` is formally étale if and
only if both cohomology sheaves of its naive cotangent complex vanish,
`H^{-1}(NL_{X/S}) = H^0(NL_{X/S}) = 0`.

Both directions are proved. The degree `0` clause is an equivalence outright: `H^0(NL_{X/S})` is
`Ω_{X/S}` by [Stacks Project, Tag 0D0J], and `Ω_{X/S} = 0` is formal unramifiedness by
[Stacks Project, Tag 02H9]. The degree `-1` clause is read stalkwise, where it is the vanishing
of `H¹` of the cotangent complex of the stalk algebra.

## Main results

* `Stacks.Smooth.formallyEtale_iff_isZero_homology_naiveCotangentComplex`:
  **[Stacks Project, Tag 0D0M]**, `f` is formally étale if and only if
  `H^{-1}(NL_{X/S}) = H^0(NL_{X/S}) = 0`.
* `Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallyEtale`: the forward
  implication, that a formally étale morphism has both cohomology sheaves of its naive cotangent
  complex zero.
* `Stacks.Smooth.formallyEtale_of_isZero_homology_naiveCotangentComplex`: the converse.
* `Stacks.Smooth.isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified`: the degree
  `0` clause of the tag on its own — `H^0(NL_{X/S}) = 0` if and only if `f` is formally
  unramified.
* `Stacks.Smooth.formallySmooth_appLE_of_formallySmooth_stalkMap` and
  `Stacks.Smooth.formallyEtale_of_formallySmooth_appLE`: the two steps the converse is assembled
  from, each stated for an arbitrary formally unramified morphism.

## Route

The forward implication is the source's own argument with nothing left out. A formally étale
morphism is formally smooth and formally unramified, which is [Stacks Project, Tag 02HH],
`AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified`. Formal smoothness
gives `H^{-1}(NL_{X/S}) = 0`, which is the degree `-1` clause of the forward implication of
[Stacks Project, Tag 0D0L],
`Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`. No bridge
between presentations of formal smoothness is needed: the `AlgebraicGeometry.FormallySmooth`
that 02HH produces and the `Stacks.Smooth.FormallySmoothScheme` that the 0D0L clause consumes
are abbreviations of the same lifting property against affine first-order thickenings, so the
witness passes straight through. Formal unramifiedness gives
`Ω_{X/S} = 0` by [Stacks Project, Tag 02H9], and `Ω_{X/S}` is `H^0(NL_{X/S})` by
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`, the degree-zero clause of
[Stacks Project, Tag 0D0J]. The source cites [Stacks Project, Tag 04FE] here instead of 02H9;
either gives `Ω_{X/S} = 0`, and 02H9 is the shorter road in this library because it is stated
as an equivalence with exactly that vanishing.

The converse takes a different road from the source, and a shorter one. The source deduces
formal *smoothness* of `f` from the converse of [Stacks Project, Tag 0D0L] — legitimate, since
`Ω_{X/S} = 0` is locally projective — and then concludes by [Stacks Project, Tag 02HH]. But the
converse of [Stacks Project, Tag 0D0L] rests on the implication `3 → 1` of
[Stacks Project, Tag 0D0F], whose torsor argument needs [Stacks Project, Tag 04FJ] in its
unrestricted sheaf form. Both clauses of 04FJ are available in that form —
`Stacks.Thickenings.exists_addAction_compatibleLifts` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomAction.lean` and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomTransitivity.lean`
— and the passage from them to `Stacks.Smooth.IsLiftPseudoTorsor`, whose lifts are those of a
lifting problem over `f` rather than the compatible lifts of [Stacks Project, Tag 04FI], is
`Stacks.Smooth.isLiftPseudoTorsor`: Tag 04FJ read for the identity thickening `𝟙 X` of the
target, where the datum of [Stacks Project, Tag 04FH] is zero and the third condition of 04FI is
vacuous. So `Stacks.Smooth.formallySmooth_of_formallySmooth_appLE` and
`Stacks.Smooth.formallySmooth_tfae` carry no torsor hypothesis, and 0D0F is unconditional. The
converse of 0D0L is proved on that footing, as
`Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero` in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothConverse`; nothing *here*
carries `@[stacks 0D0L]` because nothing here is a statement of that tag.

The torsor is not needed for formal étaleness anyway, because its whole purpose is to correct
local lifts into agreeing ones and a formally étale morphism has *unique* lifts. So the converse
is proved directly, in three steps.

1. `H^0(NL_{X/S}) = 0` makes `f` formally unramified, as above.
2. Together with `H^{-1}(NL_{X/S}) = 0` this makes every stalk map of `f` formally smooth. The
   degree `-1` vanishing is, stalkwise, injectivity of the map `I/I² ⟶ Ω` of the canonical
   presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x`
   (`Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff`, which is
   [Stacks Project, Tag 0D09] together with the stalkwise nature of exactness,
   [Stacks Project, Tag 01AG]); that injectivity is the vanishing of `H¹` of the cotangent
   complex, which for a formally unramified `f` *is* formal smoothness of the stalk map, by
   `Stacks.NaiveCotangentEtale.formallySmooth_stalkMap_iff_injective_cotangentComplex`.
3. Formal smoothness of the stalk maps of a formally unramified morphism is formal smoothness on
   every pair of compatible affine opens,
   `Stacks.Smooth.formallySmooth_appLE_of_formallySmooth_stalkMap`; and a formally unramified
   morphism which is formally smooth on affine charts is formally étale,
   `Stacks.Smooth.formallyEtale_of_formallySmooth_appLE`, because the local lifts of
   `Stacks.Smooth.exists_isAffineOpen_lift_of_formallySmooth_appLE` are then unique and so glue
   by `Stacks.Smooth.exists_lift_of_isOpenCover`.

## Implementation notes

Step 3's first half is where formal unramifiedness earns its keep a second time. Formal
smoothness of a ring map is not in general detected by the localizations of its target at
primes, and `Algebra.smoothLocus_eq_univ_iff` is available only under
`Algebra.FinitePresentation`, which the tag does not grant. The *étale* locus, however, is the
complement of the supports of `Ω[A⁄R]` and of `H¹(L_{A/R})`, so
`Algebra.etaleLocus_eq_univ_iff` is unconditional; and because `Ω[A⁄R] = 0` here, the étale and
smooth loci of a chart coincide. See the docstring of
`Stacks.Smooth.formallySmooth_appLE_of_formallySmooth_stalkMap`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9)
* [Stacks Project, Tag 02HH](https://stacks.math.columbia.edu/tag/02HH)
* [Stacks Project, Tag 04FE](https://stacks.math.columbia.edu/tag/04FE)
* [Stacks Project, Tag 04FF](https://stacks.math.columbia.edu/tag/04FF)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0D0M](https://stacks.math.columbia.edu/tag/0D0M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Smooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The degree `0` clause of [Stacks Project, Tag 0D0M], as an equivalence.** The degree `0`
cohomology sheaf of the naive cotangent complex of `f` vanishes exactly when `f` is formally
unramified. That sheaf is `Ω_{X/S}` by the degree-zero clause of [Stacks Project, Tag 0D0J],
and the vanishing of `Ω_{X/S}` is formal unramifiedness by [Stacks Project, Tag 02H9]. -/
theorem isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified :
    IsZero ((Scheme.naiveCotangentComplex f).homology 0) ↔ FormallyUnramified f := by
  rw [Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials f]
  exact ⟨fun h ↦ h.of_iso (Scheme.naiveCotangentComplexHomologyZeroIso f).symm,
    fun h ↦ h.of_iso (Scheme.naiveCotangentComplexHomologyZeroIso f)⟩

/-- **The degree `0` half of the converse of [Stacks Project, Tag 0D0M].** If the degree `0`
cohomology sheaf of the naive cotangent complex of `f` vanishes then `f` is formally
unramified.

This is one of the two halves the source's converse splits into; the other, that the degree
`-1` vanishing supplies the existence of infinitesimal lifts, is
`Stacks.Smooth.formallyEtale_of_isZero_homology_naiveCotangentComplex`, which consumes this
one. -/
theorem formallyUnramified_of_isZero_homology_zero_naiveCotangentComplex
    (h : IsZero ((Scheme.naiveCotangentComplex f).homology 0)) : FormallyUnramified f :=
  (isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified f).mp h

/-- **The forward implication of [Stacks Project, Tag 0D0M].** A formally étale morphism of
schemes has both cohomology sheaves of its naive cotangent complex zero:
`H^{-1}(NL_{X/S}) = H^0(NL_{X/S}) = 0`.

This is the source's argument. A formally étale morphism is formally smooth and formally
unramified, [Stacks Project, Tag 02HH]; formal smoothness kills `H^{-1}(NL_{X/S})` by the
forward implication of [Stacks Project, Tag 0D0L], and formal unramifiedness kills
`H^0(NL_{X/S}) = Ω_{X/S}` by [Stacks Project, Tag 02H9] and [Stacks Project, Tag 0D0J]. -/
theorem isZero_homology_naiveCotangentComplex_of_formallyEtale (hf : FormallyEtale f) :
    IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
      IsZero ((Scheme.naiveCotangentComplex f).homology 0) := by
  obtain ⟨hsm, hun⟩ := (formallyEtale_iff_formallySmooth_and_formallyUnramified f).mp hf
  exact ⟨isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth f hsm,
    (isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified f).mpr hun⟩

/-- **For a formally unramified morphism, formal smoothness of every stalk map is formal
smoothness on every pair of affine charts.** If `f : X ⟶ S` is formally unramified and all its
stalk maps `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` are formally smooth, then for affine opens `U ⊆ X`, `V ⊆ S`
with `f(U) ⊆ V` the ring map `Γ(S, V) ⟶ Γ(X, U)` is formally smooth.

Formal smoothness of a ring map is *not* in general detected by its localizations at the primes
of the target; what makes the passage legitimate here is formal unramifiedness. For
`R = Γ(S, V)` and `A = Γ(X, U)`, formal unramifiedness of `f` gives `Ω[A⁄R] = 0`, so
`Algebra.unramifiedLocus R A` is everything (`Algebra.unramifiedLocus_eq_univ_iff`), while
`AlgebraicGeometry.formallySmooth_stalkMap_iff` turns formal smoothness of the stalk map at a
point of `U` into membership of the corresponding prime in `Algebra.smoothLocus R A`, and every
prime of `A` is the prime of a point of `U` because `U` is isomorphic to `Spec A`.
So `Algebra.etaleLocus R A`, which is the intersection of the two loci, is
everything, and `Algebra.etaleLocus_eq_univ_iff` — an equivalence with no finiteness hypothesis,
because the étale locus is the complement of the supports of `Ω[A⁄R]` and of
`H¹(L_{A/R})` — makes `A` a formally étale, hence formally smooth, `R`-algebra. -/
theorem formallySmooth_appLE_of_formallySmooth_stalkMap [FormallyUnramified f]
    (hstalk : ∀ x : X, (f.stalkMap x).hom.FormallySmooth) (U : X.Opens) (hU : IsAffineOpen U)
    (V : S.Opens) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (f.appLE V U hUV).hom.FormallySmooth := by
  let := (f.appLE V U hUV).hom.toAlgebra
  have hunram : Algebra.FormallyUnramified Γ(S, V) Γ(X, U) :=
    FormallyUnramified.formallyUnramified_appLE f hV hU hUV
  have hsmooth : Algebra.smoothLocus Γ(S, V) Γ(X, U) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨x, hxp⟩ := (Scheme.homeoOfIso hU.isoSpec).surjective p
    have hp : hU.primeIdealOf x = p := hxp
    have h := (formallySmooth_stalkMap_iff V hV U hU hUV x.2).mp (hstalk x.1)
    rwa [show (⟨x.1, x.2⟩ : U) = x from rfl, hp] at h
  have hetale : Algebra.FormallyEtale Γ(S, V) Γ(X, U) := by
    refine Algebra.etaleLocus_eq_univ_iff.mp ?_
    rw [Algebra.etaleLocus_eq_unramfiedLocus_inter_smoothLocus, hsmooth,
      Algebra.unramifiedLocus_eq_univ_iff.mpr hunram, Set.univ_inter]
  exact (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp hetale).2

/-- **A formally unramified morphism that is formally smooth on affine charts is formally
étale.** If every pair of compatible affine opens gives a formally smooth ring map and `f` is
formally unramified, then every lifting problem along a first-order thickening of affine schemes
has exactly one solution.

This is the implication `3 → 1` of [Stacks Project, Tag 0D0F] in the case where the correction
step of the source's proof is vacuous, so it runs without the pseudo-torsor
`Stacks.Smooth.IsLiftPseudoTorsor`: lifts exist over an affine open neighbourhood of every
point of `T'` by `Stacks.Smooth.exists_isAffineOpen_lift_of_formallySmooth_appLE`, and formal
unramifiedness makes any two lifts over one open agree
(`AlgebraicGeometry.FormallyUnramified.hom_ext` applied to the restricted thickening
`i ∣_ (V' j ⊓ V' k)`), which is exactly the compatibility
`Stacks.Smooth.exists_lift_of_isOpenCover` asks for. The same uniqueness is the `∃!`.

Compare `AlgebraicGeometry.formallyEtale_of_unramified_flat`, [Stacks Project, Tag 04FF], which
is this argument with the local lifts produced from flatness instead. -/
theorem formallyEtale_of_formallySmooth_appLE [FormallyUnramified f]
    (hf : ∀ U : X.Opens, IsAffineOpen U → ∀ V : S.Opens, IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth) :
    FormallyEtale f := by
  intro T T' _ _ i hi p g hcomm
  have hci : IsClosedImmersion i := hi.1
  choose V' hV'affine htV' b hbf hba using
    exists_isAffineOpen_lift_of_formallySmooth_appLE f hf hi g p hcomm
  have hcover : TopologicalSpace.IsOpenCover V' :=
    top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, htV' x⟩
  have hbb : ∀ j k : T', T'.homOfLE (inf_le_left : V' j ⊓ V' k ≤ V' j) ≫ b j =
      T'.homOfLE (inf_le_right : V' j ⊓ V' k ≤ V' k) ≫ b k := by
    intro j k
    have hres : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
        (i ∣_ (V' j ⊓ V' k)) ≫ T'.homOfLE e ≫ b l = (i ⁻¹ᵁ (V' j ⊓ V' k)).ι ≫ g := by
      intro l e
      rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba l,
        ← Category.assoc, Scheme.homOfLE_ι]
    have hresf : ∀ (l : T') (e : V' j ⊓ V' k ≤ V' l),
        (T'.homOfLE e ≫ b l) ≫ f = (V' j ⊓ V' k).ι ≫ p := by
      intro l e
      rw [Category.assoc, hbf l, ← Category.assoc, Scheme.homOfLE_ι]
    have hthick := isFirstOrderThickening_morphismRestrict hi (V' j ⊓ V' k)
    have hci' : IsClosedImmersion (i ∣_ (V' j ⊓ V' k)) := hthick.1
    exact FormallyUnramified.hom_ext (i ∣_ (V' j ⊓ V' k)) ⟨2, hthick.2⟩ f
      (by rw [hres j inf_le_left, hres k inf_le_right])
      (by rw [hresf j inf_le_left, hresf k inf_le_right])
  obtain ⟨c, hc₁, hc₂⟩ := exists_lift_of_isOpenCover f i g p V' hcover b hbf hba hbb
  exact ⟨c, ⟨hc₂, hc₁⟩, fun d hd => lift_unique f hi hd.2 hc₁ hd.1 hc₂⟩

/-- **The converse of [Stacks Project, Tag 0D0M].** If both cohomology sheaves of the naive
cotangent complex of `f : X ⟶ S` vanish, `H^{-1}(NL_{X/S}) = H^0(NL_{X/S}) = 0`, then `f` is
formally étale.

The degree `0` vanishing is formal unramifiedness,
`Stacks.Smooth.isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified`. Together with
the degree `-1` vanishing it makes every stalk map of `f` formally smooth: `H^{-1}(NL_{X/S}) = 0`
is, stalkwise, the vanishing of `H¹` of the cotangent complex of `𝒪_{X,x}` over
`(f^{-1}𝒪_S)_x` by `Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff`
([Stacks Project, Tag 0D09]), and for a formally unramified `f` that vanishing *is* formal
smoothness of the stalk map, by
`Stacks.NaiveCotangentEtale.formallySmooth_stalkMap_iff_injective_cotangentComplex` — the
differentials of the stalk algebra being zero, hence projective. Formal smoothness on affine
charts then follows by
`Stacks.Smooth.formallySmooth_appLE_of_formallySmooth_stalkMap`, and
`Stacks.Smooth.formallyEtale_of_formallySmooth_appLE` assembles the local lifts.

The source argues instead through the converse of [Stacks Project, Tag 0D0L]: the degree `0`
vanishing makes `Ω_{X/S} = 0` locally projective, so the two conditions of that tag hold and `f`
is formally smooth, and then [Stacks Project, Tag 02HH] gives formal étaleness. That road is
available — the converse of [Stacks Project, Tag 0D0L] is
`Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero` —
but it is not taken here: in the formally étale case uniqueness of lifts replaces the torsor
of [Stacks Project, Tag 04FJ] that the implication `3 → 1` of [Stacks Project, Tag 0D0F] runs on,
and the detour through formal smoothness of `f` is not needed at all. -/
theorem formallyEtale_of_isZero_homology_naiveCotangentComplex
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1)))
    (hzero : IsZero ((Scheme.naiveCotangentComplex f).homology 0)) :
    FormallyEtale f := by
  have : FormallyUnramified f :=
    (isZero_homology_zero_naiveCotangentComplex_iff_formallyUnramified f).mp hzero
  refine formallyEtale_of_formallySmooth_appLE f fun U hU V hV hUV =>
    formallySmooth_appLE_of_formallySmooth_stalkMap f (fun x => ?_) U hU V hV hUV
  exact (Stacks.NaiveCotangentEtale.formallySmooth_stalkMap_iff_injective_cotangentComplex f
      x).mpr
    ((Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff f).mp hneg x)

/-- **[Stacks Project, Tag 0D0M].** A morphism of schemes `f : X ⟶ S` is formally étale if and
only if both cohomology sheaves of its naive cotangent complex vanish,
`H^{-1}(NL_{X/S}) = H^0(NL_{X/S}) = 0`.

The forward implication is
`Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallyEtale` and the converse is
`Stacks.Smooth.formallyEtale_of_isZero_homology_naiveCotangentComplex`. -/
@[stacks 0D0M]
theorem formallyEtale_iff_isZero_homology_naiveCotangentComplex :
    FormallyEtale f ↔
      IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
        IsZero ((Scheme.naiveCotangentComplex f).homology 0) :=
  ⟨isZero_homology_naiveCotangentComplex_of_formallyEtale f,
    fun h => formallyEtale_of_isZero_homology_naiveCotangentComplex f h.1 h.2⟩

end Stacks.Smooth

end
