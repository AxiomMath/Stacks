module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInverse
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.ClosedImmersionExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GroupStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The weighting attached to a relative zero-cycle over a discrete valuation ring

Let `R` be a discrete valuation ring and let `p : W ⟶ Spec R` be locally of finite type,
locally quasi-finite and quasi-compact. The function `w_γ` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting` attached to a relative `0`-cycle
`γ` on `W/Spec R` is a weighting of `p`.

## Main results

* `Stacks.Chow.isWeighting_relativeCycleWeight_of_isDiscreteValuationRing` — over the spectrum
  of a discrete valuation ring the function `w_γ` attached to a relative `0`-cycle is a
  weighting.

## Implementation notes

Over a discrete valuation ring every relative `0`-cycle is a combination of the cycle classes
`[Z/W/Spec R]_0` of members of `Hilb(W/Spec R, 0)` (Tag 0H5A,
`Stacks.Chow.surjective_relativeCycleClassMap`), so the statement follows by induction on the
free abelian group on `Hilb(W/Spec R, 0)` from the case of a single member, the construction
`γ ↦ w_γ` being additive and the weightings of a fixed morphism forming a subgroup of the
integer-valued functions on its source.

For a single member `Z ⊆ W` the function `w_{[Z/W/Spec R]_0}` is the extension by zero along
the closed immersion `Z ⟶ W` of the canonical weighting
`AlgebraicGeometry.flatQuasiFiniteWeight` of Tag 0F3D attached to `Z ⟶ Spec R`, which is flat
and locally of finite presentation by the definition of `Hilb(W/Spec R, 0)` and locally
quasi-finite because `W ⟶ Spec R` is. The identification is pointwise: the coefficient of the
fibre cycle `[Z_s]_0` at a point is the length of the local ring of `Z_s` there, and that local
ring is the quotient of the local ring of `Z` by the extension of the maximal ideal of the base,
whose length is the length factor of `flatQuasiFiniteWeight`; the inseparable-degree factors
agree because the residue field map of a closed immersion is an isomorphism.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Lemma 0H5A](https://stacks.math.columbia.edu/tag/0H5A)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The residue field map at a point of a closed immersion is surjective, the stalk map of a
closed immersion being surjective. -/
private theorem relativeCycleWeightDvrSurjective_residueFieldMap {T U : Scheme.{u}}
    (k : T ⟶ U) [IsClosedImmersion k] (t : T) :
    Function.Surjective (k.residueFieldMap t) := by
  intro b
  obtain ⟨a, ha⟩ := T.residue_surjective t b
  obtain ⟨c, hc⟩ := SurjectiveOnStalks.stalkMap_surjective k t a
  refine ⟨U.residue (k t) c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply, hc, ha]

/-- At a point of a closed subscheme the residue field extension over the base of a morphism
has the same inseparable degree as the one at the image point. -/
private theorem relativeCycleWeightDvrFinInsepDegree_eq {T U V : Scheme.{u}} (k : T ⟶ U)
    [IsClosedImmersion k] (π : U ⟶ V) (t : T) :
    (letI := ((k ≫ π).residueFieldMap t).hom.toAlgebra;
      (Field.finInsepDegree (V.residueField ((k ≫ π) t)) (T.residueField t) : ℤ)) =
      (letI := (π.residueFieldMap (k t)).hom.toAlgebra;
        (Field.finInsepDegree (V.residueField (π (k t))) (U.residueField (k t)) : ℤ)) := by
  rw [Scheme.residueFieldMap_comp k π t]
  let : Algebra (V.residueField ((k ≫ π) t)) (U.residueField (k t)) :=
    (π.residueFieldMap (k t)).hom.toAlgebra
  let : Algebra (V.residueField ((k ≫ π) t)) (T.residueField t) :=
    (π.residueFieldMap (k t) ≫ k.residueFieldMap t).hom.toAlgebra
  have hbij : Function.Bijective (k.residueFieldMap t).hom :=
    ⟨(k.residueFieldMap t).hom.injective,
      relativeCycleWeightDvrSurjective_residueFieldMap k t⟩
  let e : U.residueField (k t) ≃ₐ[V.residueField ((k ≫ π) t)] T.residueField t :=
    { RingEquiv.ofBijective (k.residueFieldMap t).hom hbij with
      commutes' := fun r ↦ (CommRingCat.comp_apply _ _ r).symm }
  exact congrArg _ (Field.finInsepDegree_eq_of_equiv _ _ _ e.symm)

/-- The length of the local fibre ring at a point is the length of the local ring of the
scheme-theoretic fibre at the corresponding point. -/
private alias relativeCycleWeightDvrFiberStalkLength :=
    AlgebraicGeometry.localFiberLength_eq_fiberStalkLength

/-- The two projections of the pullback of a closed immersion and a fibre inclusion agree in the
ambient scheme. -/
private theorem relativeCycleWeightDvr_apply_fst_eq_apply_snd {X S Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) (s : S) (η : (pullback i (f.fiberι s) : Scheme.{u})) :
    i (pullback.fst i (f.fiberι s) η) = f.fiberι s (pullback.snd i (f.fiberι s) η) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun m : (pullback i (f.fiberι s) : Scheme.{u}) ⟶ X ↦ m η)
      (pullback.condition (f := i) (g := f.fiberι s))

/-- The function attached to the family of fibre cycles of a closed subscheme vanishes at every
point outside the closed subscheme. -/
private theorem relativeCycleWeightDvr_eq_zero_of_notMem_range {X S Z : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (x : X)
    (hx : x ∉ Set.range i) :
    relativeCycleWeight f (familyAssociatedToClosedSubscheme f i 0) x = 0 := by
  rw [relativeCycleWeight_apply]
  have hcoeff : (familyAssociatedToClosedSubscheme f i 0 (f x) :
      AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) = 0 := by
    refine familyAssociatedToClosedSubscheme_apply_coeff_eq_zero f i 0 (f x) (f.asFiber x) ?_
    rintro ⟨ξ, hξ, -⟩
    refine hx ⟨pullback.fst i (f.fiberι (f x)) ξ.1, ?_⟩
    rw [relativeCycleWeightDvr_apply_fst_eq_apply_snd]
    show f.fiberι (f x) (fiberClosedImmersion f i (f x) ξ.1) = x
    rw [hξ, Scheme.Hom.fiberι_asFiber]
  rw [hcoeff, zero_mul]

/-- Alias of `Stacks.Chow.componentMultiplicity_eq_length_stalk`. -/
private alias relativeCycleWeightDvrComponentMultiplicity :=
  componentMultiplicity_eq_length_stalk

/-- The local ring of the fibre of a closed subscheme over a point of the base, computed inside
the fibre of the ambient morphism, is the local ring of the fibre of the structure morphism of
the subscheme. -/
private theorem relativeCycleWeightDvrStalkLength_fiber {X S Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)
    (η : (pullback i (f.fiberι (f (i z))) : Scheme.{u}))
    (hη : pullback.snd i (f.fiberι (f (i z))) η = f.asFiber (i z)) :
    Module.length ((pullback i (f.fiberι (f (i z))) : Scheme.{u}).presheaf.stalk η)
        ((pullback i (f.fiberι (f (i z))) : Scheme.{u}).presheaf.stalk η) =
      Module.length (((i ≫ f).fiber ((i ≫ f) z)).presheaf.stalk ((i ≫ f).asFiber z))
        (((i ≫ f).fiber ((i ≫ f) z)).presheaf.stalk ((i ≫ f).asFiber z)) := by
  let e : (pullback i (f.fiberι (f (i z))) : Scheme.{u}) ≅ (i ≫ f).fiber ((i ≫ f) z) :=
    pullbackRightPullbackFstIso f (S.fromSpecResidueField (f (i z))) i
  have hh : e.hom ≫ (i ≫ f).fiberι ((i ≫ f) z) = pullback.fst i (f.fiberι (f (i z))) :=
    pullbackRightPullbackFstIso_hom_fst f (S.fromSpecResidueField (f (i z))) i
  have hz : pullback.fst i (f.fiberι (f (i z))) η = z :=
    (Scheme.Hom.isClosedEmbedding i).injective
      (by rw [relativeCycleWeightDvr_apply_fst_eq_apply_snd, hη, Scheme.Hom.fiberι_asFiber])
  have hpt : e.hom η = (i ≫ f).asFiber z := by
    refine ((i ≫ f).fiberι ((i ≫ f) z)).isEmbedding.injective ?_
    rw [Scheme.Hom.fiberι_asFiber, ← Scheme.Hom.comp_apply, hh, hz]
  have hlen := Module.length_eq_of_ringEquiv
    (Iso.commRingCatIsoToRingEquiv (asIso (e.hom.stalkMap η)))
  rw [hpt] at hlen
  exact hlen.symm

/-- At a point of a closed subscheme with zero-dimensional fibres over the base, the function
attached to the family of fibre cycles of the subscheme is the canonical length–inseparable
degree weighting of the structure morphism of the subscheme. -/
private theorem relativeCycleWeightDvr_apply_of_mem_range {X S Z : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : ∀ s : S,
      topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤ (0 : WithBot ℕ∞))
    (z : Z) :
    relativeCycleWeight f (familyAssociatedToClosedSubscheme f i 0) (i z) =
      flatQuasiFiniteWeight (i ≫ f) z := by
  have hmem : f.asFiber (i z) ∈ Set.range (fiberClosedImmersion f i (f (i z))) := by
    show f.asFiber (i z) ∈ Set.range (pullback.snd i (f.fiberι (f (i z))))
    rw [Scheme.Pullback.range_snd i (f.fiberι (f (i z)))]
    exact ⟨z, (Scheme.Hom.fiberι_asFiber f (i z)).symm⟩
  obtain ⟨η, hη, hcoeff⟩ :=
    cycleAssociatedToClosedSubscheme_apply_eq_componentMultiplicity_of_mem_range
      (fieldChowSituation (S.residueField (f (i z))))
      (f.fiberToSpecResidueField (f (i z))) (fiberClosedImmersion f i (f (i z)))
      ((0 : ℕ) : ℤ)
      (fiberClosedSubscheme_schemeDeltaDimension_le f i 0 hdim (f (i z))) hmem
      (by
        simpa using
          relativeDimension_fiber_eq_zero_of_locallyQuasiFinite f (f (i z)) (f.asFiber (i z)))
  have hlen : (familyAssociatedToClosedSubscheme f i 0 (f (i z)) :
      AlgebraicCycle (f.fiber (f (i z))) ℤ) (f.asFiber (i z)) =
      ((Module.length (Z.presheaf.stalk z) ((Z.presheaf.stalk z) ⧸
        Ideal.map ((i ≫ f).stalkMap z).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk ((i ≫ f) z))))).toNat : ℤ) := by
    rw [show (familyAssociatedToClosedSubscheme f i 0 (f (i z)) :
          AlgebraicCycle (f.fiber (f (i z))) ℤ) (f.asFiber (i z)) =
        componentMultiplicity (fiberClosedImmersion f i (f (i z))) η from hcoeff,
      relativeCycleWeightDvrComponentMultiplicity,
      relativeCycleWeightDvrStalkLength_fiber f i z η.1 hη,
      ← relativeCycleWeightDvrFiberStalkLength (i ≫ f) z]
  have hfq : flatQuasiFiniteWeight (i ≫ f) z =
      ((Module.length (Z.presheaf.stalk z) ((Z.presheaf.stalk z) ⧸
          Ideal.map ((i ≫ f).stalkMap z).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk ((i ≫ f) z))))).toNat : ℤ) *
        (let := (f.residueFieldMap (i z)).hom.toAlgebra;
          (Field.finInsepDegree (S.residueField (f (i z))) (X.residueField (i z)) : ℤ)) := by
    rw [← relativeCycleWeightDvrFinInsepDegree_eq i f z]
    rfl
  rw [relativeCycleWeight_apply, hfq, hlen]

/-- Over the spectrum of a discrete valuation ring it is enough to know that the function
attached to the cycle class of a single member of `Hilb(W/Spec R, 0)` is a weighting: every
relative `0`-cycle is a combination of such classes by Tag 0H5A, and the construction of the
function is additive while the weightings form a subgroup. -/
private theorem relativeCycleWeightDvrIsWeighting_of_generators {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hgen : ∀ Z : HilbertCycleDatum p 0,
      IsWeighting p (relativeCycleWeight p (Z.cycleFamily p)))
    (γ : FamilyOfCycles p 0) (hγ : IsRelativeCycle p 0 γ) :
    IsWeighting p (relativeCycleWeight p γ) := by
  obtain ⟨β, hβ⟩ := surjective_relativeCycleClassMap (r := 0) p ⟨γ, hγ⟩
  have hγeq : γ = cycleClassMap p 0 β := by
    rw [← relativeCycleClassMap_val p β, hβ]
  rw [hγeq]
  clear hγeq hβ
  induction β using FreeAbelianGroup.induction_on with
  | zero =>
    rw [map_zero, relativeCycleWeight_zero]
    intro U V h π g comm hg hU hπ
    exact isWeighting_zero p h π g comm hg hU hπ
  | of Z =>
    rw [cycleClassMap_of]
    intro U V h π g comm hg hU hπ
    exact hgen Z h π g comm hg hU hπ
  | neg Z h =>
    rw [map_neg, relativeCycleWeight_neg]
    intro U V h' π g comm hg hU hπ
    exact IsWeighting.neg h h' π g comm hg hU hπ
  | add a b ha hb =>
    rw [map_add, relativeCycleWeight_add]
    intro U V h π g comm hg hU hπ
    exact IsWeighting.add ha hb h π g comm hg hU hπ

/-- The function attached to the family of fibre cycles of a member of `Hilb(X/S, 0)` is a
weighting: on the member it is the canonical length–inseparable-degree weighting of its
structure morphism, which is flat, locally of finite presentation and locally quasi-finite, and
off the member it vanishes. -/
private theorem relativeCycleWeightDvrIsWeighting_cycleFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    (Z : HilbertCycleDatum f 0) :
    IsWeighting f (relativeCycleWeight f (Z.cycleFamily f)) := by
  have hflat := Z.flat
  have hfp := Z.locallyFinitePresentation
  have hqf : LocallyQuasiFinite (Z.ideal.subschemeι ≫ f) := inferInstance
  have hdim : ∀ s : S, topologicalKrullDim
      (pullback Z.ideal.subschemeι (f.fiberι s) : Scheme.{u}) ≤ (0 : WithBot ℕ∞) :=
    fun s ↦ by simpa using Z.topologicalKrullDim_pullback_fiberι_le f s
  rw [Z.cycleFamily_eq_familyAssociatedToClosedSubscheme f]
  intro U V h π g comm hg hU hπ
  exact IsWeighting.extendByZero_of_isClosedImmersion Z.ideal.subschemeι
    (flatQuasiFiniteWeight_isWeighting (Z.ideal.subschemeι ≫ f)) _
    (fun x hx ↦ relativeCycleWeightDvr_eq_zero_of_notMem_range f Z.ideal.subschemeι x hx)
    (fun z ↦ relativeCycleWeightDvr_apply_of_mem_range f Z.ideal.subschemeι hdim z)
    h π g comm hg hU hπ

/-- **Stacks Project, Tag 0H5P.** Over the spectrum of a discrete valuation ring, the function
`w_α` attached to a relative `0`-cycle is a weighting.

Every relative `0`-cycle over a discrete valuation ring is a combination of the cycle classes
of members of `Hilb(W/Spec R, 0)` by Tag 0H5A, the construction `α ↦ w_α` is additive, and the
weightings of a fixed morphism are closed under the group operations; so it suffices to treat a
single member `Z`, where `w` is the extension by zero along `Z ⊆ W` of the canonical weighting
of Tag 0F3D attached to the flat, locally quasi-finite morphism `Z ⟶ Spec R`. -/
theorem isWeighting_relativeCycleWeight_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType p] [LocallyQuasiFinite p] [QuasiCompact p]
    (γ : FamilyOfCycles p 0) (hγ : IsRelativeCycle p 0 γ) :
    AlgebraicGeometry.IsWeighting p (relativeCycleWeight p γ) := by
  exact relativeCycleWeightDvrIsWeighting_of_generators p
    (fun Z ↦ relativeCycleWeightDvrIsWeighting_cycleFamily p Z) γ hγ

end Stacks.Chow

end
