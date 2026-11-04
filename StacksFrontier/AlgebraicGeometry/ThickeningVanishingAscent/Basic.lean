module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleDepthFourVanishing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher direct images ascends along a thickening

Let

```
Y --j'--> Y'
|g        |g'
T --j---> T'
```

be cartesian with `g'` proper, flat and of finite presentation, `j` a thickening and `M'` an
invertible `𝒪_{Y'}`-module.  If the higher direct images of `(j')^* M'` along `g` vanish, then
those of `M'` along `g'` vanish.  The hypothesis is downstairs, over the thin scheme `T`, and the
conclusion is upstairs: this is an **ascent**, in the direction opposite to base change.

## Main results

* `Stacks.AlgebraicGeometry.ThickeningVanishingAscent.isZero_of_isZero_pullback_of_surjective`:
  a module of finite type whose pullback along a **surjective** morphism vanishes is zero.
* `Stacks.AlgebraicGeometry.ThickeningVanishingAscent.isPullback_restrict` and
  `.restrictPullbackResLEIso`: the cartesian square and the module on its source, restricted over
  an open of `T'`.
* `Stacks.AlgebraicGeometry.ThickeningVanishingAscent`
  `.isZero_rightDerivedPlus_pushforward_of_isZero_pullback_of_compactSpace`: the ascent over a
  quasi-compact base, which is where the induction runs.
* `Stacks.AlgebraicGeometry.ThickeningVanishingAscent`
  `.isZero_rightDerivedPlus_pushforward_of_isZero_pullback`: the ascent over an arbitrary base.

## The argument, and why it needs neither [Stacks, Tag 0B91] nor [Stacks, Tag 0BDK]

The source of [Stacks, Tag 0D4F] performs this step by making `Rg'_* (M')^{⊗ d}` a **perfect**
object whose formation commutes with base change ([Stacks, Tag 0B91] (1)), identifying its
pullback with a finite locally free module in degree `0` ([Stacks, Tag 0D4E]) and transporting
that back up along `j` by the universal property of [Stacks, Tag 0BDK].  The perfection half of
[Stacks, Tag 0B91] is absent from this library and [Stacks, Tag 0BDK] is proved only along open
immersions, so that route is closed.  **It is not needed.**

* **The comparison.** `g'` is flat, so `AlgebraicGeometry.torIndependent_of_flat_left` makes the
  square Tor independent and [Stacks, Tag 08IB]
  (`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_torIndependent`, unconditional) gives
  `Lj^* Rg'_* K ≅ Rg_* L(j')^* K`.  At `K = M'[0]` the right-hand side is `Rg_*(((j')^*M')[0])`,
  because `M'` is invertible hence flat and
  `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` turns its derived
  pullback into the ordinary one.  The hypothesis puts that in `D^{≤0}`.  This is the same
  observation that discharges `hvan`: **the tensor-form-only blockage of [Stacks, Tag 0B91] is
  about a canonical comparison, and a vanishing conclusion does not need one** — any isomorphism
  of objects will do.
* **The ascent is false without finiteness.** `Stacks.Thickenings.IsThickening` is a closed
  immersion that is surjective; its kernel ideal is *not* nilpotent (that is
  `IsFiniteOrderThickening`).  With `A = k[t^{1/2ⁿ} : n]/(t)` and `I = (t^{1/2ⁿ} : n)` one has
  `I = I²`, so `Spec (A/I) ⟶ Spec A` is a thickening, and the `A`-module `M = I` has
  `j^* M = I/I² = 0` with `M ≠ 0`.  So no argument that only pulls a vanishing back along `j`
  can work; the cohomology sheaf must be known to be of finite type.
* **Finiteness comes from pseudo-coherence, not perfection.**
  `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_of_flat_of_isProper` is
  [Stacks, Tag 0CSD] with no hypothesis, at exactly `g'` flat, proper and locally of finite
  presentation, which is what this situation grants.  Pseudo-coherence is strictly weaker than
  the perfection the library records as absent, and it is enough:
  `AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom`
  ([Stacks, Tag 08DN] (1)) makes the **top** non-vanishing cohomology sheaf of finite type.
* **Localisation.** [Stacks, Tag 01XJ] starts the induction and needs the base quasi-compact; no
  form of it in the library does without that, and pseudo-coherence gives only *local* bounds.
  So the induction is run over each affine open `V` of `T'` and the conclusion globalised, which
  is legitimate because vanishing of a higher direct image is local on the base.  The cartesian
  square restricts by `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`, the hypothesis and the
  conclusion travel between `T'` and `V` by [Stacks, Tag 01E5], and `restrictPullbackResLEIso`
  matches the module on the restricted source.
* **The induction.** Over a quasi-compact base [Stacks, Tag 01XJ] gives a degree `B` above which
  every higher direct image along `g'` vanishes, so `K = Rg'_*(M'[0])` lies in `D^{≤B}`.
  Descending from `B`: at the top degree `m > 0`,
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback` — in its
  generic `IsLE` form, not the `TopDegreeBaseChangeSituation` one, which is what lets it be used
  when only *this* module is known to vanish above `m` — identifies `H ᵐ(Lj^* K)` with
  `j^* H ᵐ(K)`.  The left side vanishes, `H ᵐ(K)` is of finite type, and
  `isZero_of_isZero_pullback_of_surjective` forces `H ᵐ(K) = 0`.  The induction steps down to
  `D^{≤0}`, which is the conclusion.

## Implementation notes

**The Nakayama step is three existing lemmas.** All of its content is already inside
[Stacks, Tag 056J]: `SheafOfModules.supp_pullback` says the support of a pullback of a
finite-type module is the preimage of the support — that is where Nakayama is used — and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.notMem_supp_of_isZero_pullback` packages it for an
arbitrary morphism.  Only **surjectivity** of `j` is then needed, so the lemma below is stated
with `Function.Surjective` rather than with `Stacks.Thickenings.IsThickening`: the
closed-immersion half would be an unused hypothesis.

**Instances supplied positionally.** As elsewhere in this cluster, instance search unifies only
at reducible transparency, where `AlgebraicGeometry.Scheme.Modules` does not unfold to
`SheafOfModules (structureSheafRing _)`; the `IsLE` and `IsIso` facts are therefore bound with
explicit types and passed with `@`.

`HasDerivedCategory.standard` is activated at priority `10000`, as in every file of this cluster.

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.AlgebraicGeometry.ThickeningVanishingAscent

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The Nakayama step -/

/-- **A module of finite type whose pullback along a surjective morphism vanishes is zero.**

Everything substantive is [Stacks, Tag 056J]: the support of the pullback of a finite-type
module is the preimage of the support, which is where Nakayama's lemma is used, and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.notMem_supp_of_isZero_pullback` states it for an
arbitrary morphism.  Surjectivity then empties the support.

Only surjectivity is assumed; for a thickening it is `Stacks.Thickenings.IsThickening.2`, and the
closed-immersion half is not used. -/
theorem isZero_of_isZero_pullback_of_surjective {T T' : Scheme.{u}} (j : T ⟶ T')
    (hj : Function.Surjective j) (F : T'.Modules) (hft : F.IsFiniteType)
    (h : IsZero ((Scheme.Modules.pullback j).obj F)) :
    IsZero F := by
  refine _root_.AlgebraicGeometry.isZero_of_forall_isZero_stalk F fun y => ?_
  obtain ⟨x, rfl⟩ := hj y
  exact (notMem_supp_iff_isZero_stalk F (j x)).mp
    (notMem_supp_of_isZero_pullback F hft j x h)

/-! ### The downward induction -/

/-- **The induction that carries the vanishing up.**  Let `K` be a pseudo-coherent object of
`D(𝒪_{T'})` lying in `D^{≤B}`, and let `j : T ⟶ T'` be surjective.  If the cohomology of
`Lj^* K` vanishes in every positive degree, then so does the cohomology of `K` itself.

At the top degree `m`, `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.derivedPullbackTopDegreeIsoPullback` identifies `H ᵐ(Lj^* K)` with `j^* H ᵐ(K)`; the former
vanishes, `H ᵐ(K)` is of finite type by [Stacks, Tag 08DN] (1), and
`isZero_of_isZero_pullback_of_surjective` kills it.  The induction then steps down by one
degree.

`K` is written out at every occurrence rather than left to unification: with it elided the
elaborator re-unifies the three spellings of the category of modules at each step and exhausts
its heartbeats. -/
theorem isLE_zero_of_isLE_of_isPseudoCoherent {T T' : Scheme.{u}} (j : T ⟶ T')
    (hj : Function.Surjective j) (K : DerivedCategory T'.Modules)
    (hKpc : RingedSpace.IsPseudoCoherent (X := T'.toRingedSpace) K)
    (hLj : ∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor T.Modules m).obj
      ((derivedPullback j.toLRSHom.toShHom).obj K)))
    (B : ℤ) (hKB : DerivedCategory.TStructure.t.IsLE K B) :
    DerivedCategory.TStructure.t.IsLE K 0 := by
  have step : ∀ m : ℤ, 0 < m → DerivedCategory.TStructure.t.IsLE K m →
      DerivedCategory.TStructure.t.IsLE K (m - 1) := by
    intro m hm hKm
    have habove : ∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor T'.Modules i).obj K) := fun i hi =>
      @DerivedCategory.isZero_of_isLE _ _ _ _ K m i hi hKm
    have hft : ((DerivedCategory.homologyFunctor T'.Modules m).obj K).IsFiniteType :=
      RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom K m
        (hKpc.isPseudoCoherentFrom m) habove
    have htop : IsZero ((Scheme.Modules.pullback j).obj
        ((DerivedCategory.homologyFunctor T'.Modules m).obj K)) :=
      (hLj m hm).of_iso
        (derivedPullbackTopDegreeIsoPullback j.toLRSHom.toShHom K m hKm).symm
    have hzero := isZero_of_isZero_pullback_of_surjective j hj _ hft htop
    refine (DerivedCategory.isLE_iff K (m - 1)).2 fun i hi => ?_
    rcases eq_or_lt_of_le (show m ≤ i by omega) with h | h
    · exact h ▸ hzero
    · exact habove i h
  have hle : ∀ a b : ℤ, a ≤ b → DerivedCategory.TStructure.t.IsLE K a →
      DerivedCategory.TStructure.t.IsLE K b := fun a b hab ha =>
    @CategoryTheory.Triangulated.TStructure.isLE_of_le _ _ _ _ _ _ _
      DerivedCategory.TStructure.t K a b hab ha
  have hdown : ∀ n : ℕ, DerivedCategory.TStructure.t.IsLE K (max 0 (B - n)) := by
    intro n
    induction n with
    | zero => exact hle B _ (by simp) hKB
    | succ k ih =>
      by_cases hk : 0 < max 0 (B - (k : ℤ))
      · exact hle _ _ (by push_cast; omega) (step _ hk ih)
      · have h0 : max 0 (B - ((k + 1 : ℕ) : ℤ)) = max 0 (B - (k : ℤ)) := by push_cast; omega
        exact h0 ▸ ih
  have h := hdown B.toNat
  rwa [show max 0 (B - (B.toNat : ℤ)) = 0 by omega] at h

/-! ### The ascent -/

/-- **Vanishing of the higher direct images ascends along a surjective base change, for a
proper flat morphism of finite presentation and an invertible module.**

The hypothesis is the vanishing of `R ᵖ g_* ((j')^* M')` for every `p > 0` downstairs; the
conclusion is the vanishing of `R ᵖ g'_* M'` upstairs.  See the module documentation for why
neither the perfection half of [Stacks, Tag 0B91] nor [Stacks, Tag 0BDK] is needed, and for the
counterexample showing that the finiteness supplied by [Stacks, Tag 0CSD] cannot be dispensed
with. -/
theorem isZero_rightDerivedPlus_pushforward_of_isZero_pullback_of_compactSpace
    {Y Y' T T' : Scheme.{u}} {g : Y ⟶ T} {g' : Y' ⟶ T'} {j : T ⟶ T'} {j' : Y ⟶ Y'}
    (hj : Function.Surjective j) (hsq : IsPullback j' g g' j)
    [IsProper g'] [Flat g'] [LocallyOfFinitePresentation g'] [CompactSpace T']
    (M' : Y'.Modules) [IsInvertibleModule Y' M']
    (hvan : ∀ q : ℤ, 0 < q →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
        ((Scheme.Modules.pullback j').obj M')))
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward g').rightDerivedPlus p).obj M') := by
  have hM'qc : M'.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule M'
  set E := (DerivedCategory.singleFunctor Y'.Modules 0).obj M' with hEdef
  set K := (derivedPushforward g'.toLRSHom.toShHom).obj E with hKdef
  -- `E` has quasi-coherent cohomology and is pseudo-coherent, being perfect.
  have hEqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor Y'.Modules n).obj E).IsQuasicoherent :=
    _root_.AlgebraicGeometry.isQuasicoherent_homology_singleFunctor_obj Y' M' hM'qc
  have hinvS : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj
      Y'.ringCatSheaf.property M' := ‹IsInvertibleModule Y' M'›
  have hEpc : RingedSpace.IsPseudoCoherent (X := Y'.toRingedSpace) E :=
    Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E
      (_root_.AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree Y' M'
        (Stacks.Divisors.isFiniteLocallyFree_of_isInvertible Y' M'))
  -- [Stacks, Tag 0CSD]: `K = Rg'_* E` is pseudo-coherent.
  have hKpc : RingedSpace.IsPseudoCoherent (X := T'.toRingedSpace) K :=
    _root_.AlgebraicGeometry.isPseudoCoherent_derivedPushforward_of_flat_of_isProper g' E hEpc
  -- [Stacks, Tag 08IB]: the square is Tor independent because `g'` is flat.
  have hbc := _root_.AlgebraicGeometry.isIso_derivedBaseChangeMap_of_torIndependent hsq
    (_root_.AlgebraicGeometry.torIndependent_of_flat_left g' j) E hEqc
  -- Downstairs, `Rg_*(((j')^* M')[0])` lies in `D^{≤0}`.
  have h1 : DerivedCategory.TStructure.t.IsLE
      ((derivedPushforward g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj
          ((modulePullback j'.toLRSHom.toShHom).obj M'))) 0 :=
    isLE_derivedPushforward_singleFunctor g.toLRSHom.toShHom _ 0 (fun q hq => hvan q hq)
  -- Hence the cohomology of `Lj^* K` vanishes in every positive degree.
  have hLj : ∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor T.Modules m).obj
      ((derivedPullback j.toLRSHom.toShHom).obj K)) := by
    intro m hm
    refine (@DerivedCategory.isZero_of_isLE _ _ _ _ _ 0 m hm h1).of_iso
      ((DerivedCategory.homologyFunctor T.Modules m).mapIso
        (@asIso _ _ _ _ (derivedBaseChangeMap j'.toLRSHom.toShHom g.toLRSHom.toShHom
            g'.toLRSHom.toShHom j.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) E) hbc ≪≫
          (derivedPushforward g.toLRSHom.toShHom).mapIso
            (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso
              j'.toLRSHom.toShHom M'
              (Stacks.SheafOfModules.isFlat_of_isInvertible (X := Y'.toRingedSpace) M'
                inferInstance))))
  -- [Stacks, Tag 01XJ] starts the induction.
  obtain ⟨B, hB⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward g'
  have hKB : DerivedCategory.TStructure.t.IsLE K B :=
    isLE_derivedPushforward_singleFunctor g'.toLRSHom.toShHom M' B
      (fun q hq => hB q (le_of_lt hq) M' hM'qc)
  have hK0 : DerivedCategory.TStructure.t.IsLE K 0 :=
    isLE_zero_of_isLE_of_isPseudoCoherent j hj K hKpc hLj B hKB
  exact isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward g' M' p
    (@DerivedCategory.isZero_of_isLE _ _ _ _ K 0 p hp hK0)

/-! ### Localisation over the base -/

/-- **Restricting the pullback along the top of the square to an open of the base.**  With
`U' = (g')⁻¹V` an open of `Y'` and `U` an open of `Y` inside `(j')⁻¹U'`, the restriction to `U` of
`(j')^* M'` is the pullback along `j'.resLE U' U` of the restriction of `M'` to `U'`.

Both sides are the pullback of `M'` along the two factorisations of one morphism `U ⟶ Y'`,
`U.ι ≫ j' = j'.resLE U' U ≫ U'.ι` (`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`), so the
comparison is two instances of `AlgebraicGeometry.Scheme.Modules.pullbackComp` with
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` between them, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at either end.  The left-hand side
is written with `modulePullback` because that is the spelling whose invertibility is an instance
([Stacks, Tag 0B8L]), the right-hand side with `restrictFunctor` because that is what
[Stacks, Tag 01E5] is stated at. -/
noncomputable def restrictPullbackResLEIso {Y Y' : Scheme.{u}} (j' : Y ⟶ Y')
    (U' : Y'.Opens) (U : Y.Opens) (hle : U ≤ j' ⁻¹ᵁ U') (M' : Y'.Modules) :
    (Scheme.Modules.pullback (j'.resLE U' U hle)).obj
        ((modulePullback U'.ι.toLRSHom.toShHom).obj M') ≅
      (Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pullback j').obj M') :=
  (Scheme.Modules.pullbackComp (j'.resLE U' U hle) U'.ι).app M' ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι j' hle)).app M' ≪≫
      ((Scheme.Modules.pullbackComp U.ι j').app M').symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
          ((Scheme.Modules.pullback j').obj M')).symm

/-- **The cartesian square restricted over an open of the base.**  This is
`AlgebraicGeometry.Scheme.Hom.isPullback_resLE` at `US = V`, `UT = j⁻¹V` and `UX = (g')⁻¹V`, with
the three `resLE`s that are taken at a full preimage rewritten to morphism restrictions by
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`. -/
theorem isPullback_restrict {Y Y' T T' : Scheme.{u}} {g : Y ⟶ T} {g' : Y' ⟶ T'} {j : T ⟶ T'}
    {j' : Y ⟶ Y'} (hsq : IsPullback j' g g' j) (V : T'.Opens)
    (hle : g ⁻¹ᵁ (j ⁻¹ᵁ V) ≤ j' ⁻¹ᵁ (g' ⁻¹ᵁ V)) :
    IsPullback (j'.resLE (g' ⁻¹ᵁ V) (g ⁻¹ᵁ (j ⁻¹ᵁ V)) hle) (g ∣_ (j ⁻¹ᵁ V)) (g' ∣_ V)
      (j ∣_ V) := by
  have h := Scheme.Hom.isPullback_resLE hsq (US := V) (UT := j ⁻¹ᵁ V) (UX := g' ⁻¹ᵁ V)
    le_rfl le_rfl (UY := g ⁻¹ᵁ (j ⁻¹ᵁ V)) (by rw [inf_eq_right.2 hle])
  rwa [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_eq_morphismRestrict] at h

/-- **Vanishing of the higher direct images ascends along a surjective base change**, with no
hypothesis on the base.

Vanishing of a higher direct image is local on the base, so it is enough to check it over each
affine open `V` of `T'`; an affine scheme is quasi-compact, so
`isZero_rightDerivedPlus_pushforward_of_isZero_pullback_of_compactSpace` applies there.  The
cartesian square restricts by `isPullback_restrict`, the hypothesis and the conclusion are carried
between `T'` and `V` by [Stacks, Tag 01E5]
(`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`), and the module on
the restricted source is matched by `restrictPullbackResLEIso`.

This is what removes the quasi-compactness the induction needs: no form of [Stacks, Tag 01XJ] in
the library gives a bound over a base that is not quasi-compact, and pseudo-coherence gives only
local bounds, so the induction has to be run on each member of a cover. -/
theorem isZero_rightDerivedPlus_pushforward_of_isZero_pullback
    {Y Y' T T' : Scheme.{u}} {g : Y ⟶ T} {g' : Y' ⟶ T'} {j : T ⟶ T'} {j' : Y ⟶ Y'}
    (hj : Surjective j) (hsq : IsPullback j' g g' j)
    [IsProper g'] [Flat g'] [LocallyOfFinitePresentation g']
    (M' : Y'.Modules) [IsInvertibleModule Y' M']
    (hvan : ∀ q : ℤ, 0 < q →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus q).obj
        ((Scheme.Modules.pullback j').obj M')))
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward g').rightDerivedPlus p).obj M') := by
  obtain ⟨pn, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
  refine isZero_of_isZero_restrict_cover (fun V : T'.affineOpens => V.1)
    (_root_.AlgebraicGeometry.iSup_affineOpens_eq_top T') _ fun V => ?_
  have : IsAffine (V.1).toScheme := V.2
  have _hjV : Surjective (j ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) hj V.1
  -- The two opens upstairs agree, because the square commutes.
  have hUeq : g ⁻¹ᵁ (j ⁻¹ᵁ V.1) = j' ⁻¹ᵁ (g' ⁻¹ᵁ V.1) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq.w]
  have hres := isZero_rightDerivedPlus_pushforward_of_isZero_pullback_of_compactSpace
    _hjV.1 (isPullback_restrict hsq V.1 hUeq.le)
    ((modulePullback (g' ⁻¹ᵁ V.1).ι.toLRSHom.toShHom).obj M') ?hyp pn hp
  · exact hres.of_iso
      ((_root_.AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso g' V.1 M'
          pn).symm ≪≫
        ((Scheme.Modules.pushforward (g' ∣_ V.1)).rightDerivedPlus (pn : ℤ)).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback (g' ⁻¹ᵁ V.1).ι).app M'))
  · -- The hypothesis, restricted over `V`.
    intro q hq
    obtain ⟨qn, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, by omega⟩
    refine ((Functor.map_isZero (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V.1).ι)
      (hvan (qn : ℤ) hq)).of_iso
      (_root_.AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso g
        (j ⁻¹ᵁ V.1) ((Scheme.Modules.pullback j').obj M') qn)).of_iso ?_
    exact ((Scheme.Modules.pushforward (g ∣_ (j ⁻¹ᵁ V.1))).rightDerivedPlus (qn : ℤ)).mapIso
      (restrictPullbackResLEIso j' (g' ⁻¹ᵁ V.1) (g ⁻¹ᵁ (j ⁻¹ᵁ V.1)) hUeq.le M')

end Stacks.AlgebraicGeometry.ThickeningVanishingAscent

end
