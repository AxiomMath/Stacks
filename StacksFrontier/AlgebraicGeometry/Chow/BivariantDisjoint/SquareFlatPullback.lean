module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an open subscheme commutes with flat pullback

Let `q : A ⟶ B` be a flat morphism of relative dimension `r` between schemes locally of finite
type over the base scheme of chapter 42 of the Stacks Project, and let `mB : B' ⟶ B` and
`mA : A' ⟶ A` be open immersions fitting into a cartesian square

  `A' --q'--> B'`
  `|mA         |mB`
  `A  --q-->  B`

so that `q' : A' ⟶ B'` is again flat of relative dimension `r`. Restricting cycles, or Chow
classes, to the open subschemes then commutes with flat pullback:

  `(q^* α)|_{A'} = (q')^* (α|_{B'})`   in   `Z_{k+r}(A')`, resp. `A_{k+r}(A')`.

This is the special case of Stacks 02RD and Stacks 02RG — flat pullback is functorial, and
commutes with proper pushforward in a cartesian square — in which the two horizontal legs are
open immersions. Neither general statement is in this repository; this case is, and it is proved
directly from the coefficient formula of Stacks 02RB rather than by specializing anything. The
case of two isomorphism legs is
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange`, and the case in which
the *vertical* leg is proper is
`Stacks.Chow.chowGroupOpensRestrict_properChowPushforward` in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward`.

Restriction along an open immersion only reindexes coefficients, so the whole content is that the
flat pullback multiplicity `Stacks.Chow.flatPullbackWeight` of a point of `A'` for `q'` equals the
multiplicity of its image in `A` for `q`. Both are read off a closed subscheme of the ambient
scheme, and an open immersion of the ambient scheme changes neither the generic points of that
subscheme lying over the point nor their multiplicities: the generic points of an open subspace
are exactly the generic points of the ambient space that lie in it, and the stalk of the
subscheme at such a point is unchanged.

## Main results

* `Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding` — a point of an open subspace is the
  generic point of one of its irreducible components exactly when its image is the generic point
  of an irreducible component of the ambient space.
* `Stacks.Chow.componentMultiplicity_eq_of_isOpenImmersion_ambient`,
  `Stacks.Chow.closedSubschemeCycleCoeff_of_isOpenImmersion_ambient`,
  `Stacks.Chow.closedSubschemeCycleCoeff_comap_of_isOpenImmersion` — the multiplicity of a
  component of a closed subscheme, and the coefficient of its cycle, are unchanged by restricting
  the ambient scheme along an open immersion.
* `Stacks.Chow.flatPullbackWeight_eq_of_isOpenImmersion_square` — the flat pullback multiplicity
  is unchanged by restricting both source and target of the flat morphism along open immersions.
* `Stacks.Chow.cycleGroupRestrict_flatPullback` — **the open-immersion case of Stacks 02RD and
  Stacks 02RG**, on cycle groups.
* `Stacks.Chow.chowGroupRestrict_flatPullbackChow` — the same identity on Chow groups.

## References

* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

open TopologicalSpace

/-! ### Generic points of an open subspace -/

/-- **The generic points of an open subspace are the generic points of the ambient space that
lie in it.** For an open embedding `g`, the closure of `{w}` is an irreducible component of the
source exactly when the closure of `{g w}` is an irreducible component of the target.

From right to left this is the preimage of an irreducible component along an open embedding. From
left to right, enlarge the closure of `{g w}` to an irreducible component `V`: its preimage is an
irreducible component of the source containing the closure of `{w}`, hence equal to it, and `V`
is the closure of the image of its own preimage, so `V` is the closure of `{g w}`. -/
@[ega "0 2.1.6" "partial"]
theorem mem_genericPoints_iff_of_isOpenEmbedding {W Z : Type u} [TopologicalSpace W]
    [TopologicalSpace Z] {g : W → Z} (hg : Topology.IsOpenEmbedding g) (w : W) :
    w ∈ genericPoints W ↔ g w ∈ genericPoints Z := by
  have hpre : g ⁻¹' closure ({g w} : Set Z) = closure ({w} : Set W) := by
    rw [hg.isOpenMap.preimage_closure_eq_closure_preimage hg.continuous]
    congr 1
    ext y
    simp [hg.injective.eq_iff]
  refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
  · obtain ⟨V, hV, hVsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({g w} : Set Z)) isIrreducible_singleton.closure
    have hVclosed : IsClosed V := isClosed_of_mem_irreducibleComponents V hV
    have hgw : g w ∈ V := hVsub (subset_closure rfl)
    have hmax : g ⁻¹' V ⊆ closure ({w} : Set W) :=
      hw.2 (preimage_mem_irreducibleComponents hV hg ⟨g w, hgw, w, rfl⟩).1
        (closure_minimal (by simpa using hgw) (hVclosed.preimage hg.continuous))
    have hVeq : V = closure ({g w} : Set Z) := by
      refine subset_antisymm ?_ hVsub
      rw [← closure_image_preimage_of_isPreirreducible g hg.isOpenMap V ⟨w, hgw⟩ hV.1.2 hVclosed]
      refine closure_minimal ?_ isClosed_closure
      refine (Set.image_mono hmax).trans ?_
      refine (image_closure_subset_closure_image hg.continuous).trans ?_
      simp
    show closure ({g w} : Set Z) ∈ irreducibleComponents Z
    exact hVeq ▸ hV
  · have h := preimage_mem_irreducibleComponents hw hg ⟨g w, subset_closure rfl, w, rfl⟩
    rwa [hpre] at h

/-! ### Cycles of a closed subscheme after restricting the ambient scheme -/

/-- A commuting square of schemes commutes on underlying points. -/
private theorem base_apply_eq_of_comp_eq {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (x : X) :
    g.base (f.base x) = g'.base (f'.base x) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun t : X ⟶ Z ↦ t.base x) h

/-- **Multiplicity does not see an open immersion of the ambient scheme.** If `g : W ⟶ Z` is an
open immersion and `p : W ⟶ A'`, `i : Z ⟶ A` are closed immersions, the multiplicity of the
component of `W` with generic point `ξ` equals the multiplicity of the component of `Z` with
generic point `g ξ`.

Multiplicity is the length of the stalk of the subscheme at that point over itself, by
`Stacks.Chow.componentMultiplicity_eq_length_stalk`, and an open immersion induces an
isomorphism on stalks. -/
theorem componentMultiplicity_eq_of_isOpenImmersion_ambient {A A' Z W : Scheme.{u}}
    (i : Z ⟶ A) [IsClosedImmersion i] (p : W ⟶ A') [IsClosedImmersion p]
    (g : W ⟶ Z) [IsOpenImmersion g] (ξ : genericPoints W)
    (hη : g.base ξ.1 ∈ genericPoints Z) :
    componentMultiplicity p ξ = componentMultiplicity i ⟨g.base ξ.1, hη⟩ := by
  let S : Type u := Z.presheaf.stalk (g.base ξ.1)
  let R : Type u := W.presheaf.stalk ξ.1
  let _ : Algebra S R := (g.stalkMap ξ.1).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap S R) :=
    (asIso (g.stalkMap ξ.1)).commRingCatIsoToRingEquiv.bijective
  have h1 : Module.length S S = Module.length S R :=
    (LinearEquiv.ofBijective (Algebra.linearMap S R) hbij).length_eq
  have h2 : Module.length S R = Module.length R R :=
    Module.length_eq_of_surjective hbij.surjective
  rw [componentMultiplicity_eq_length_stalk, componentMultiplicity_eq_length_stalk]
  exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (h1.trans h2).symm

/-- **The coefficient of the cycle of a closed subscheme does not see an open immersion of the
ambient scheme.** Let `m : A' ⟶ A` be an open immersion over the base and let a closed immersion
`p : W ⟶ A'` sit over a closed immersion `i : Z ⟶ A` through an open immersion `g : W ⟶ Z` whose
range is the inverse image of the range of `m`. Then the coefficient of `[W ⊆ A']_k` at a point
of `A'` is the coefficient of `[Z ⊆ A]_k` at its image.

Both coefficients are multiplicities of components, and the generic points of `W` lying over the
point correspond to the generic points of `Z` lying over its image by
`Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding`, with equal multiplicities by
`Stacks.Chow.componentMultiplicity_eq_of_isOpenImmersion_ambient`; delta-dimension is unchanged
because `m` is an open immersion over the base. -/
theorem closedSubschemeCycleCoeff_of_isOpenImmersion_ambient (C : ChowSituation.{u})
    {A A' Z W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S)
    [LocallyOfFiniteType sA'] (m : A' ⟶ A) [IsOpenImmersion m] (hm : m ≫ sA = sA')
    (i : Z ⟶ A) [IsClosedImmersion i] (p : W ⟶ A') [IsClosedImmersion p]
    (g : W ⟶ Z) [IsOpenImmersion g] (hsq : p ≫ m = g ≫ i)
    (hrange : Set.range g.base = i.base ⁻¹' Set.range m.base) (k : ℤ) (x' : A') :
    closedSubschemeCycleCoeff C sA' p k x' =
      closedSubschemeCycleCoeff C sA i k (m.base x') := by
  have hdim : relativeDimension C.dimensionFunction sA' x' =
      relativeDimension C.dimensionFunction sA (m.base x') := by
    rw [← hm, relativeDimension_comp_isOpenImmersion]
  have hpt : ∀ w : W, m.base (p.base w) = i.base (g.base w) :=
    base_apply_eq_of_comp_eq hsq
  show (cycleAssociatedToClosedSubscheme C sA' p k).1 x' =
    (cycleAssociatedToClosedSubscheme C sA i k).1 (m.base x')
  by_cases hW : ∃ ξ : genericPoints W,
      p.base ξ.1 = x' ∧ relativeDimension C.dimensionFunction sA' x' = k
  · obtain ⟨ξ, rfl, hd⟩ := hW
    have hgξ : g.base ξ.1 ∈ genericPoints Z :=
      (mem_genericPoints_iff_of_isOpenEmbedding g.isOpenEmbedding ξ.1).mp ξ.2
    rw [cycleAssociatedToClosedSubscheme_apply C sA' p k ξ hd, hpt,
      cycleAssociatedToClosedSubscheme_apply C sA i k ⟨g.base ξ.1, hgξ⟩
        (by rwa [← hpt ξ.1, ← hdim])]
    exact componentMultiplicity_eq_of_isOpenImmersion_ambient i p g ξ hgξ
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C sA' p k x' hW,
      cycleAssociatedToClosedSubscheme_apply_eq_zero C sA i k (m.base x') ?_]
    rintro ⟨η, hη, hd⟩
    obtain ⟨w, hw⟩ : η.1 ∈ Set.range g.base := by
      rw [hrange]
      exact ⟨x', hη.symm⟩
    exact hW ⟨⟨w, (mem_genericPoints_iff_of_isOpenEmbedding g.isOpenEmbedding w).mpr (hw ▸ η.2)⟩,
      m.isOpenEmbedding.injective ((hpt w).trans (hw ▸ hη)), hdim.trans hd⟩

/-- **Restricting the ambient scheme along an open immersion over the base does not change the
coefficients of the cycle of a closed subscheme.** For an ideal sheaf `I` on `A` the inverse image
`I.comap m` cuts out the part of the subscheme of `I` lying over `A'`, and the coefficient of its
cycle at a point of `A'` is the coefficient of the cycle of `I` at the image point.

The identification of the subscheme of `I.comap m` with an open subscheme of the subscheme of `I`
is `Scheme.IdealSheafData.comapIso` followed by the base change of `m`, whose range is the inverse
image of the range of `m` by `AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`. -/
theorem closedSubschemeCycleCoeff_comap_of_isOpenImmersion (C : ChowSituation.{u})
    {A A' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S)
    [LocallyOfFiniteType sA'] (m : A' ⟶ A) [IsOpenImmersion m] (hm : m ≫ sA = sA')
    (I : A.IdealSheafData) (k : ℤ) (x' : A') :
    closedSubschemeCycleCoeff C sA' (I.comap m).subschemeι k x' =
      closedSubschemeCycleCoeff C sA I.subschemeι k (m.base x') := by
  have hsq : (I.comap m).subschemeι ≫ m =
      ((I.comapIso m).hom ≫ pullback.snd m I.subschemeι) ≫ I.subschemeι := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hsurj : Function.Surjective (I.comapIso m).hom.base :=
    (Scheme.homeoOfIso (I.comapIso m)).surjective
  have hrange : Set.range ((I.comapIso m).hom ≫ pullback.snd m I.subschemeι).base =
      I.subschemeι.base ⁻¹' Set.range m.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ,
      AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd]
    rfl
  exact closedSubschemeCycleCoeff_of_isOpenImmersion_ambient C sA sA' m hm I.subschemeι
    (I.comap m).subschemeι _ hsq hrange k x'

/-! ### The weight of the flat pullback after restricting to open subschemes -/

/-- **The flat pullback multiplicity is unchanged by restricting to open subschemes.** In a
commuting square `mA ≫ q = q' ≫ mB` over the base whose horizontal legs `mA` and `mB` are open
immersions, the multiplicity `Stacks.Chow.flatPullbackWeight` of a point of `A'` for `q'` is the
multiplicity of its image in `A` for `q`.

The reduced closure of `q' x'` in `B'` is the inverse image along `mB` of the reduced closure of
`mB (q' x')` in `B`, by `Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`; the square
then identifies the two scheme-theoretic inverse images, and the coefficient of the cycle of a
closed subscheme does not see the open immersion `mA` of the ambient scheme. -/
theorem flatPullbackWeight_eq_of_isOpenImmersion_square (C : ChowSituation.{u})
    {A A' B B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S)
    [LocallyOfFiniteType sA'] (q : A ⟶ B) (q' : A' ⟶ B') (mA : A' ⟶ A) [IsOpenImmersion mA]
    (hmA : mA ≫ sA = sA') (mB : B' ⟶ B) [IsOpenImmersion mB] (hw : mA ≫ q = q' ≫ mB)
    (j : ℤ) (x' : A') :
    flatPullbackWeight C sA' q' j x' = flatPullbackWeight C sA q j (mA.base x') := by
  have hpt : q.base (mA.base x') = mB.base (q'.base x') := base_apply_eq_of_comp_eq hw x'
  have hmB' : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({mB.base (q'.base x')} : Set B))).comap mB =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({q'.base x'} : Set B')) :=
    comap_integralComponentAt_of_isOpenImmersion mB (q'.base x')
  have hJ : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({q'.base x'} : Set B'))).comap q' =
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({q.base (mA.base x')} : Set B))).comap q).comap mA := by
    rw [hpt, ← hmB', ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hw]
  rw [flatPullbackWeight, flatPullbackWeight,
    closedSubschemeCycleCoeff_congr_idealSheaf C sA' hJ j x',
    closedSubschemeCycleCoeff_comap_of_isOpenImmersion C sA sA' mA hmA _ j x']

/-! ### The open-immersion case of Stacks 02RD and Stacks 02RG -/

/-- **The open-immersion case of Stacks 02RD and Stacks 02RG, on cycle groups.** In a square
`mA ≫ q = q' ≫ mB` over the base whose horizontal legs are open immersions and whose vertical
legs are flat of relative dimension `r`, restriction of cycles commutes with flat pullback.

Both sides are given by the coefficient formula of Stacks 02RB: the coefficient of the cycle at
the image point, times the multiplicity. The two scalars agree because the square commutes, and
the two multiplicities agree by
`Stacks.Chow.flatPullbackWeight_eq_of_isOpenImmersion_square`. -/
theorem cycleGroupRestrict_flatPullback (C : ChowSituation.{u}) {A B A' B' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension q r) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (hmA : mA ≫ sA = sA') (mB : B' ⟶ B) [IsOpenImmersion mB] (hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') [LocallyOfFiniteType q'] [Flat q'] (hq' : q' ≫ sB' = sA')
    (hw : mA ≫ q = q' ≫ mB) (hr' : AlgebraicGeometry.RelativeDimension q' r) (k : ℤ)
    (α : CycleGroup C sB k) :
    cycleGroupRestrict C sA sA' mA hmA (k + (r : ℤ))
        (flatPullback C sA sB q hq r hr k α) =
      flatPullback C sA' sB' q' hq' r hr' k (cycleGroupRestrict C sB sB' mB hmB k α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x' ↦ ?_)
  have hpt : q.base (mA.base x') = mB.base (q'.base x') := base_apply_eq_of_comp_eq hw x'
  rw [cycleGroupRestrict_apply, flatPullback_apply, flatPullback_apply,
    cycleGroupRestrict_apply,
    flatPullbackWeight_eq_of_isOpenImmersion_square C sA sA' q q' mA hmA mB hw
      (k + (r : ℤ)) x', hpt]

/-- **The open-immersion case of Stacks 02RD and Stacks 02RG, on Chow groups.** In a cartesian
square over the base whose horizontal legs `mA` and `mB` are open immersions and whose vertical
leg `q` is flat of relative dimension `r`, restriction of Chow classes to the open subschemes
commutes with flat pullback.

Both maps are induced on quotients by the corresponding maps of cycle groups, so this is
`Stacks.Chow.cycleGroupRestrict_flatPullback` read on representatives. -/
theorem chowGroupRestrict_flatPullbackChow (C : ChowSituation.{u}) {A B A' B' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension q r) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (hmA : mA ≫ sA = sA') (mB : B' ⟶ B) [IsOpenImmersion mB] (hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') (hq' : q' ≫ sB' = sA')
    (hsq : CategoryTheory.IsPullback mA q' q mB) :
    letI : LocallyOfFiniteType q' :=
      MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat q' := MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension q' r) (k : ℤ)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB q hq r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sB' q' hq' r hr' k)
      (α : chowGroup C sB k),
      chowGroupRestrict C sA sA' mA hmA (k + (r : ℤ))
          (flatPullbackChow C sA sB q hq r hr k hfac α) =
        flatPullbackChow C sA' sB' q' hq' r hr' k hfac'
          (chowGroupRestrict C sB sB' mB hmB k α) := by
  have : LocallyOfFiniteType q' :=
    MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
  have : Flat q' := MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
  intro hr' k hfac hfac' α
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sA' (k + (r : ℤ))))
      (cycleGroupRestrict_flatPullback C sA sB sA' sB' q hq r hr mA hmA mB hmB q' hq' hsq.w
        hr' k c)

end Stacks.Chow

end
