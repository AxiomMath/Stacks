module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GenericFibres
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertFlatness
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.PointClosure
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LowerSemicontinuity

/-!
# Every relative cycle over a discrete valuation ring is a cycle class

Let `R` be a discrete valuation ring, let `S = Spec R` and let `f : X ⟶ S` be of finite type.
Then every relative `r`-cycle on `X/S` is a combination of the cycle classes `[Z/X/S]_r` of
members of `Hilb(X/S, r)`; that is, the cycle-class homomorphism of Equation 0H58 is surjective.

The proof is the source's. A relative `r`-cycle `α` is determined by its member over the generic
point `η` of `S` (Tag 0H55), and that member is a finite combination `∑ nᵢ [ξᵢ]` of points of the
generic fibre `X_η` of relative dimension `r`. For each such point take the closure of its image
in `X` with the reduced induced structure: that closed subscheme is integral and dominates `S`,
hence is flat over the discrete valuation ring `R`, and its generic fibre is the reduced closure
of `ξᵢ` in `X_η`, of dimension `r`; lower semicontinuity of the dimension of the fibres of a flat
morphism of finite presentation (Tag 0D4H) then bounds the dimension of the special fibre by `r`
as well. So it is a member of `Hilb(X/S, r)` whose class has `[ξᵢ]` as its member over `η`, and
`∑ nᵢ` of these classes agrees with `α` over `η`, hence equals `α`.

## Main results

* `Stacks.Chow.exists_cycleClassMap_apply_genericPoint_eq` — over a discrete valuation ring every
  `r`-cycle on the generic fibre is the generic member of a cycle class of Tag 0H6V.
* `Stacks.Chow.surjective_relativeCycleClassMap` — **Stacks Project, Lemma 0H5A**: the
  cycle-class homomorphism of Equation 0H58 into `z(X/S, r)` is surjective.

## Implementation notes

The source assumes `f` of finite type. The statements below assume exactly that,
`LocallyOfFiniteType f` and `QuasiCompact f`; the homomorphism of Equation 0H58 needs only the
first, `Spec R` being locally Noetherian, and the finite-presentation instance that the members
of `Hilb(X/Spec R, r)` and the homomorphism of Tag 0H6V use is found by instance search, through
Mathlib's instance deducing `AlgebraicGeometry.LocallyOfFinitePresentation` from
`AlgebraicGeometry.LocallyOfFiniteType` over a locally Noetherian base.

The surjectivity statement for the homomorphism of Tag 0H6V is
`Stacks.Chow.exists_cycleClassMap_apply_genericPoint_eq`, and it is transferred to Equation 0H58
along `Stacks.Chow.relativeCycleClassMap_val`, which identifies the two homomorphisms. That the
values of Equation 0H58 lie in `z(X/S, r)` at all is Tag 0H56 applied to the structure sheaf of
a member of `Hilb(X/S, r)`, which is flat over the base at every point of `X` by
`Stacks.Chow.HilbertCycleDatum.isFlatOverInDimensionsGE_structureModule`, since flatness of
`Z ⟶ S` is part of its data.

The closure of a point `x` of `X` with the reduced induced structure is the closed subscheme cut
out by `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of the closure of `{x}`. Its
generic fibre is computed by base change along `X_η ⟶ X`, which is an open immersion because
`Spec` of the fraction field of a discrete valuation ring is the complement of the closed point;
so that base change is again a reduced closed subscheme, namely the reduced closure of the point
of the fibre, and in particular integral and of multiplicity one at its generic point. Everything
that does not use the discrete valuation ring is proved below for an arbitrary base scheme and an
arbitrary point `s` whose fibre inclusion `X_s ⟶ X` is an open immersion.

## References

* [Stacks Project, Lemma 0H5A](https://stacks.math.columbia.edu/tag/0H5A)
* [Stacks Project, Lemma 0H55](https://stacks.math.columbia.edu/tag/0H55)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Tag 0D4H](https://stacks.math.columbia.edu/tag/0D4H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The reduced closure of a point -/

/-- The support of the vanishing ideal of the closure of a point is that closure. -/
theorem coe_support_pointClosure (X : Scheme.{u}) (x : X) :
    ((AlgebraicGeometry.reducedPointIdeal X x).support : Set X) = closure ({x} : Set X) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The closure of a point with its reduced induced structure is reduced. -/
instance isReduced_pointClosure (X : Scheme.{u}) (x : X) :
    IsReduced (AlgebraicGeometry.reducedPointIdeal X x).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _

/-- The closure of a point with its reduced induced structure is an integral scheme. -/
instance isIntegral_pointClosure (X : Scheme.{u}) (x : X) :
    IsIntegral (AlgebraicGeometry.reducedPointIdeal X x).subscheme := by
  have : IrreducibleSpace (AlgebraicGeometry.reducedPointIdeal X x).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [Scheme.IdealSheafData.range_subschemeι, coe_support_pointClosure]
      exact isIrreducible_singleton.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The inclusion of the reduced closure of `x` carries its generic point to `x`. -/
theorem subschemeι_genericPoint_pointClosure (X : Scheme.{u}) (x : X) :
    (AlgebraicGeometry.reducedPointIdeal X x).subschemeι
        (genericPoint (AlgebraicGeometry.reducedPointIdeal X x).subscheme) = x :=
  image_genericPoint_eq_of_range_eq_closure _ x
    (by rw [Scheme.IdealSheafData.range_subschemeι, coe_support_pointClosure])

/-! ### The cycle of an integral closed subscheme -/

/-- An integral closed subscheme occurs in its own associated cycle with multiplicity one: the
stalk at the generic point is a field, and it is a simple module over the stalk of the ambient
scheme because the stalk map of a closed immersion is surjective. -/
private theorem multiplicity_eq_one_of_isIntegral {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (ξ : genericPoints Z) :
    componentMultiplicity i ξ = 1 := by
  classical
  let A : Type u := X.presheaf.stalk (i ξ.1)
  let B : Type u := Z.presheaf.stalk ξ.1
  let _ : Module A B := Module.compHom B (i.stalkMap ξ.1).hom
  let _ : Field B := (isField_stalk_of_closure_mem_irreducibleComponents (X := Z) ξ.1 ξ.2).toField
  have hsimple : IsSimpleModule A B := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨inferInstance, fun b hb c ↦ ?_⟩
    obtain ⟨a, ha⟩ := i.stalkMap_surjective ξ.1 (c / b)
    refine ⟨a, ?_⟩
    change (i.stalkMap ξ.1).hom a * b = c
    rw [ha, div_mul_cancel₀ c hb]
  simp [componentMultiplicity, A, B]

/-! ### Restricting the reduced closure of a point to an open subscheme -/

section OpenImmersion

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)

/-- Pulling the reduced closure of `g y` back along an open immersion `g` gives the reduced
closure of `y`: the pullback is reduced because `g` is an open immersion, and its support is the
preimage of the closure of `g y`, which is the closure of `y`. -/
private theorem comap_pointClosure :
    (AlgebraicGeometry.reducedPointIdeal X (g y)).comap g =
      AlgebraicGeometry.reducedPointIdeal Y y := by
  have : IsReduced (pullback g (AlgebraicGeometry.reducedPointIdeal X (g y)).subschemeι) :=
    isReduced_of_isOpenImmersion
      (pullback.snd g (AlgebraicGeometry.reducedPointIdeal X (g y)).subschemeι)
  have : IsReduced ((AlgebraicGeometry.reducedPointIdeal X (g y)).comap g).subscheme :=
    isReduced_of_isOpenImmersion ((AlgebraicGeometry.reducedPointIdeal X (g y)).comapIso g).hom
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  refine TopologicalSpace.Closeds.ext ?_
  rw [Scheme.IdealSheafData.support_comap]
  change (g : Y → X) ⁻¹' ((AlgebraicGeometry.reducedPointIdeal X (g y)).support : Set X) =
    closure ({y} : Set Y)
  rw [coe_support_pointClosure, ← Set.image_singleton,
    ← g.isOpenEmbedding.closure_eq_preimage_closure_image]

/-- The isomorphism between the reduced closure of `y` and the restriction to `Y` of the reduced
closure of `g y`. -/
private def pointClosureRestrictIso :
    (AlgebraicGeometry.reducedPointIdeal Y y).subscheme ≅
      pullback (AlgebraicGeometry.reducedPointIdeal X (g y)).subschemeι g :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (comap_pointClosure g y).symm) ≪≫
    (AlgebraicGeometry.reducedPointIdeal X (g y)).comapIso g ≪≫ pullbackSymmetry _ _

/-- The restriction to `Y` of the reduced closure of `g y` is integral. -/
private instance isIntegral_pullback_pointClosure :
    IsIntegral (pullback (AlgebraicGeometry.reducedPointIdeal X (g y)).subschemeι g : Scheme.{u}) :=
  IsIntegral.of_isIso (pointClosureRestrictIso g y).hom

/-- The restriction to `Y` of the reduced closure of `g y` has the closure of `y` as its image in
`Y`: the image of the second projection of a fibred product is the preimage of the image of the
first factor. -/
private theorem range_pullback_snd_pointClosure :
    Set.range (pullback.snd (AlgebraicGeometry.reducedPointIdeal X (g y)).subschemeι g : _ → Y) =
      closure ({y} : Set Y) := by
  rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι,
    coe_support_pointClosure, ← Set.image_singleton,
    ← g.isOpenEmbedding.closure_eq_preimage_closure_image]

end OpenImmersion

/-! ### The reduced closure of a point of an open fibre -/

/-- The topological Krull dimension is invariant under isomorphism of schemes. -/
private theorem topologicalKrullDim_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S)
  [IsOpenImmersion (f.fiberι s)]

/-- The fibre over `s` of the reduced closure of a point `y` of `X_s` of relative dimension `r`
has dimension `r`: it is the reduced closure of `y` inside `X_s`, whose dimension is the relative
dimension at its generic point by Stacks 02QO. -/
private theorem topologicalKrullDim_pullback_pointClosure {r : ℕ} (y : f.fiber s)
    (hy : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y = (r : ℤ)) :
    topologicalKrullDim (pullback
        (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι (f.fiberι s) :
      Scheme.{u}) = (r : WithBot ℕ∞) := by
  have : JacobsonSpace (fieldChowSituation (S.residueField s)).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of (S.residueField s))))
  rw [← topologicalKrullDim_eq_of_iso (pointClosureRestrictIso (f.fiberι s) y),
    topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation (S.residueField s))
      (fun _ _ ↦ rfl) (f.fiberToSpecResidueField s)
      (AlgebraicGeometry.reducedPointIdeal (f.fiber s) y).subschemeι
      (genericPoint (AlgebraicGeometry.reducedPointIdeal (f.fiber s) y).subscheme)
      (genericPoint_spec (AlgebraicGeometry.reducedPointIdeal (f.fiber s) y).subscheme),
    subschemeι_genericPoint_pointClosure, hy]
  simp

/-- The cycle on `X_s` of the fibre over `s` of the reduced closure of a point `y` of `X_s` of
relative dimension `r` is the prime cycle at `y`. -/
private theorem cycleAssociatedToClosedSubscheme_pullback_pointClosure_eq_single {r : ℕ}
    [DecidableEq (f.fiber s)] (y : f.fiber s)
    (hy : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y = (r : ℤ)) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
        (f.fiberToSpecResidueField s)
        (pullback.snd (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι
          (f.fiberι s)) (r : ℤ)).1 =
      Function.locallyFinsuppWithin.single y 1 := by
  have hgen : (pullback.snd
      (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι (f.fiberι s) :
      _ → f.fiber s)
      (genericPoint (pullback
          (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι (f.fiberι s) :
        Scheme.{u})) = y :=
    image_genericPoint_eq_of_range_eq_closure _ y
      (range_pullback_snd_pointClosure (f.fiberι s) y)
  rw [cycleAssociatedToClosedSubscheme_eq_single _ _ _ (r : ℤ) (by rwa [hgen]), hgen]
  congr 1
  exact Subsingleton.elim _ _

end Fibre

/-! ### Flatness over a discrete valuation ring -/

/-- An injection of a discrete valuation ring into a domain gives a flat morphism of spectra: a
torsion-free module over a discrete valuation ring is flat. -/
@[ega "0 6.3.4" "DVR base", ega "IV 21.12.17" "affine step", sga "3 XV 4.7" "special case"]
private theorem flat_specMap_of_injective {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {A : Type u} [CommRing A] [IsDomain A] (φ : R →+* A)
    (hφ : Function.Injective φ) : Flat (Spec.map (CommRingCat.ofHom φ)) := by
  let := φ.toAlgebra
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  rw [Flat.SpecMap_iff]
  exact (inferInstance : Module.Flat R A)

/-- **An integral scheme dominating the spectrum of a discrete valuation ring is flat over it.**
Flatness is Zariski-local at the source, and on a nonempty affine open `U` the morphism is `Spec`
of the injection of `R` into the domain `Γ(U)`. -/
theorem flat_of_isIntegral_of_isDominant {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of R))
    [IsDominant p] : Flat p := by
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat.{u, u})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat.{u})
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) fun U ↦ ?_
  by_cases hU : Nonempty U.1
  · have : IsIntegral U.1.toScheme := inferInstance
    have : IsDominant U.1.ι := Opens.isDominant_ι (U.1.isOpen.dense (by simpa using hU))
    have : IsSchemeTheoreticallyDominant (U.1.ι ≫ p) :=
      IsSchemeTheoreticallyDominant.of_isDominant _
    let φ : R →+* Γ(U.1.toScheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (U.1.ι ≫ p).appTop).hom
    have heq : U.1.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) = U.1.ι ≫ p := by
      change U.1.toScheme.toSpecΓ ≫ Spec.map
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (U.1.ι ≫ p).appTop) = _
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
      simp
    rw [← heq]
    exact @Flat.comp _ _ _ _ _ inferInstance (flat_specMap_of_injective φ
      (((U.1.ι ≫ p).app_injective ⊤).comp
        (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.injective))
  · exact Flat.of_stalkMap _ fun z ↦ (hU ⟨z⟩).elim

/-- The reduced closure of a point lying over the generic point of `Spec R` dominates `Spec R`,
hence is flat over the discrete valuation ring: its generic point lies over the generic point of
`Spec R`, whose closure is everything. -/
private theorem flat_pointClosure_of_apply_eq_genericPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X)
    (hx : f x = genericPoint (Spec (.of R))) :
    Flat ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f) := by
  have hgen : ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f)
      (genericPoint (AlgebraicGeometry.reducedPointIdeal X x).subscheme) =
      genericPoint (Spec (.of R)) := by
    rwa [Scheme.Hom.comp_apply, subschemeι_genericPoint_pointClosure]
  have : IsDominant ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f) := by
    constructor
    rw [denseRange_iff_closure_range]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← genericPoint_closure (α := Spec (.of R))]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)
  exact flat_of_isIntegral_of_isDominant _

/-! ### The generic fibre over a discrete valuation ring is an open subscheme -/

/-- `Spec` of the fraction field of a discrete valuation ring is an open subscheme of `Spec R`:
the fraction field is the localization away from a uniformizer. -/
private theorem isOpenImmersion_specMap_fractionField {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) ?_ ?_).mpr inferInstance
    · rintro a ⟨n, rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hirr.ne_zero)
    · intro a ha
      obtain ⟨n, unit, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp ha) hirr
      refine ⟨ϖ ^ n, ⟨n, rfl⟩, ?_⟩
      rw [heq]
      exact ⟨(unit⁻¹ : Rˣ), by rw [mul_comm (↑unit : R), mul_assoc]; simp⟩
  exact IsOpenImmersion.of_isLocalization ϖ

/-- The canonical morphism from the spectrum of the residue field at the generic point of
`Spec R`, for `R` a discrete valuation ring, is an open immersion. -/
private theorem isOpenImmersion_fromSpecResidueField_genericPoint {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  let : (genericPoint (Spec (.of R))).asIdeal.IsPrime := (genericPoint (Spec (.of R))).isPrime
  have hopen : ∀ q : PrimeSpectrum R, q = ⊥ →
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))) := by
    rintro q rfl
    change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (⊥ : Ideal R).ResidueField)))
    exact isOpenImmersion_specMap_fractionField
  have hgen : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap R (genericPoint (Spec (.of R))).asIdeal.ResidueField))) :=
    hopen _ (genericPoint_eq_bot_of_affine (.of R))
  exact @IsOpenImmersion.comp _ _ _ _ _ inferInstance hgen

/-- The inclusion of the generic fibre of a morphism to the spectrum of a discrete valuation ring
is an open immersion. -/
theorem isOpenImmersion_fiberι_genericPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    IsOpenImmersion (f.fiberι (genericPoint (Spec (.of R)))) :=
  have := isOpenImmersion_fromSpecResidueField_genericPoint (R := R)
  inferInstanceAs (IsOpenImmersion
    (pullback.fst f ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))))))

/-! ### The fibrewise data of a member of `Hilb(X/S, r)` -/

/-- Every fibre of a member of `Hilb(X/S, r)` has dimension at most `r`, in the shape in which
`Stacks.Chow.familyAssociatedToModule_pushforwardStructureSheaf_apply` asks for it: the fibre of
the closed subscheme over `t` is its fibre product with `X_t`. -/
private theorem topologicalKrullDim_pullback_hilbertCycleDatum {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (Z : HilbertCycleDatum f r) (t : S) :
    topologicalKrullDim (pullback Z.ideal.subschemeι (f.fiberι t) : Scheme.{u}) ≤
      (r : WithBot ℕ∞) := by
  refine le_of_eq_of_le ?_ (topologicalKrullDim_fiber_le_of_relativeDimensionLE
    (Z.ideal.subschemeι ≫ f) Z.relativeDimensionLE t)
  exact topologicalKrullDim_eq_of_iso (compFiberIso Z.ideal.subschemeι f t)

section Fibre2

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S)
  [IsOpenImmersion (f.fiberι s)]

/-- The fibre over `s` of the reduced closure of a point `y` of `X_s` of relative dimension `r`
has dimension `r`, read off the fibre-dimension function of the closed subscheme over the base. -/
private theorem fiberDimension_pointClosure_eq {r : ℕ} (y : f.fiber s)
    (hy : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y = (r : ℤ)) :
    ((AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι ≫ f).fiberDimension s =
      (r : WithBot ℕ∞) := by
  refine Eq.trans ?_ (topologicalKrullDim_pullback_pointClosure f s y hy)
  exact topologicalKrullDim_eq_of_iso
    (compFiberIso (AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)).subschemeι f s).symm

/-- **The class of a member of `Hilb(X/S, r)` cut out by the reduced closure of a point of an
open fibre.** Its member over `s` is the prime cycle at that point: the class is the family of
cycles of the closed subscheme, whose member over `s` is the cycle of the restriction of that
subscheme to `X_s`, and that restriction is the integral reduced closure of the point. -/
private theorem cycleFamily_eq_single_of_ideal_eq_pointClosure {r : ℕ}
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian S] [DecidableEq (f.fiber s)]
    (y : f.fiber s)
    (hy : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y = (r : ℤ)) (Z : HilbertCycleDatum f r)
    (hZ : Z.ideal = AlgebraicGeometry.reducedPointIdeal X (f.fiberι s y)) :
    (Z.cycleFamily f s).1 = Function.locallyFinsuppWithin.single y 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hval : (Z.cycleFamily f s : FiberCycleGroup f s r) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
        (f.fiberToSpecResidueField s) (pullback.snd Z.ideal.subschemeι (f.fiberι s)) (r : ℤ) :=
    familyAssociatedToModule_pushforwardStructureSheaf_apply Z.ideal.subschemeι f r
      (topologicalKrullDim_pullback_hilbertCycleDatum f Z) s
  rw [hval, hZ]
  exact cycleAssociatedToClosedSubscheme_pullback_pointClosure_eq_single f s y hy

end Fibre2

/-! ### Evaluating a cycle class over a point of the base -/

/-- The cycle-class homomorphism of Tag 0H6V evaluated over a point `s` of the base, landing in
the group of all cycles on the fibre `X_s`. -/
private def cycleClassAt {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] (r : ℕ) (s : S) :
    FreeAbelianGroup (HilbertCycleDatum f r) →+ AlgebraicCycle (f.fiber s) ℤ :=
  ((cyclesOfDimension (fieldChowSituation (S.residueField s))
      (f.fiberToSpecResidueField s) (r : ℤ)).subtype.comp
    (Pi.evalAddMonoidHom (fun t : S ↦ FiberCycleGroup f t r) s)).comp (cycleClassMap f r)

private theorem cycleClassAt_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (s : S)
    (β : FreeAbelianGroup (HilbertCycleDatum f r)) :
    cycleClassAt f r s β = (cycleClassMap f r β s).1 :=
  rfl

/-- A cycle on a quasi-compact fibre `X_s` is the member over `s` of a combination of cycle
classes as soon as every point carrying a nonzero coefficient is the member over `s` of one: the
cycle has finite support there, and it is the sum of the prime cycles at its support weighted by
its coefficients. -/
private theorem exists_cycleClassMap_apply_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (s : S) [CompactSpace (f.fiber s)]
    [DecidableEq (f.fiber s)] (c : FiberCycleGroup f s r)
    (hex : ∀ y : f.fiber s, (c.1 : AlgebraicCycle (f.fiber s) ℤ) y ≠ 0 →
      ∃ Z : HilbertCycleDatum f r,
        (Z.cycleFamily f s).1 = Function.locallyFinsuppWithin.single y 1) :
    ∃ β : FreeAbelianGroup (HilbertCycleDatum f r), cycleClassMap f r β s = c := by
  have hfin : (c.1 : AlgebraicCycle (f.fiber s) ℤ).support.Finite := by
    simpa using (Function.locallyFinsupp.locallyFiniteSupport
      (c.1 : AlgebraicCycle (f.fiber s) ℤ)).finite_inter_support_of_isCompact
        (isCompact_univ : IsCompact (Set.univ : Set (f.fiber s)))
  choose Z hZ using fun x : hfin.toFinset ↦ hex x.1 (hfin.mem_toFinset.mp x.2)
  refine ⟨∑ x ∈ hfin.toFinset.attach, c.1 x.1 • FreeAbelianGroup.of (Z x), Subtype.ext ?_⟩
  have hterm : ∀ x : hfin.toFinset,
      cycleClassAt f r s (c.1 x.1 • FreeAbelianGroup.of (Z x)) =
        Function.locallyFinsuppWithin.single x.1 (c.1 x.1) := by
    intro x
    rw [map_zsmul, cycleClassAt_apply, cycleClassMap_of, hZ x]
    refine Function.locallyFinsuppWithin.ext fun w ↦ ?_
    simp only [Function.locallyFinsuppWithin.single_apply,
      Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [← cycleClassAt_apply, map_sum]
  simp only [hterm]
  rw [Finset.sum_attach hfin.toFinset
    fun w ↦ Function.locallyFinsuppWithin.single w (c.1 w)]
  exact Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ hfin

/-! ### The member of `Hilb(X/S, r)` attached to a point of the generic fibre -/

/-- **The member of `Hilb(X/S, r)` attached to a point of the generic fibre.** For `x` a point of
`X` lying over the generic point of `Spec R` whose closure has generic fibre of dimension at most
`r`, the closure of `x` with the reduced induced structure is flat, of finite presentation and of
relative dimension at most `r` over `Spec R`.

That the special fibre has dimension at most `r` as well is Tag 0D4H: the dimension of the fibres
of a flat morphism of finite presentation is a lower semicontinuous function on the base, so the
locus where it is at most `r` is closed, and it contains the generic point of `Spec R`. -/
@[sga "6 X 7.14" "partial"]
private def pointClosureDatum {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f] {r : ℕ}
    (x : X) (hx : f x = genericPoint (Spec (.of R)))
    (hdim : ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f).fiberDimension
      (genericPoint (Spec (.of R))) ≤ (r : WithBot ℕ∞)) :
    HilbertCycleDatum f r :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI hflat : Flat ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f) :=
    flat_pointClosure_of_apply_eq_genericPoint f x hx
  { ideal := AlgebraicGeometry.reducedPointIdeal X x
    flat := hflat
    locallyFinitePresentation := inferInstance
    quasiCompact := inferInstance
    relativeDimensionLE := by
      have hclosed := (lowerSemicontinuous_fiberDimension
          ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f)
        ⟨inferInstance, inferInstance, inferInstance⟩).isClosed_preimage (r : WithBot ℕ∞)
      have hall : ∀ t : Spec (.of R),
          ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f).fiberDimension t ≤
            (r : WithBot ℕ∞) :=
        fun t ↦ ((genericPoint_spec (Spec (.of R))).mem_closed_set_iff hclosed).mp hdim
          (Set.mem_univ t)
      exact fun z ↦ (Scheme.Hom.fiberDimension_le_iff
        ((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f) _ _).mp
        (hall (((AlgebraicGeometry.reducedPointIdeal X x).subschemeι ≫ f) z)) z rfl }

/-! ### Surjectivity -/

/-- Over the spectrum of a discrete valuation ring every `r`-cycle on the generic fibre of a
finite type morphism is the generic member of a combination of the cycle classes of Tag 0H6V.

This is the content of Lemma 0H5A for the homomorphism of Tag 0H6V, whose construction needs no
flatness input. -/
theorem exists_cycleClassMap_apply_genericPoint_eq {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    [QuasiCompact f] (r : ℕ) (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    ∃ β : FreeAbelianGroup (HilbertCycleDatum f r),
      cycleClassMap f r β (genericPoint (Spec (.of R))) = c := by
  classical
  have := isOpenImmersion_fiberι_genericPoint f
  have : CompactSpace (f.fiber (genericPoint (Spec (.of R)))) := inferInstance
  refine exists_cycleClassMap_apply_eq f r (genericPoint (Spec (.of R))) c fun y hne ↦ ?_
  have hy := (mem_cyclesOfDimension_iff_forall_point _ _ _ _).mp c.2 y hne
  have hx : f (f.fiberι (genericPoint (Spec (.of R))) y) = genericPoint (Spec (.of R)) :=
    (f.fiberHomeo (genericPoint (Spec (.of R))) y).2
  exact ⟨_, cycleFamily_eq_single_of_ideal_eq_pointClosure f (genericPoint (Spec (.of R))) y hy
    (pointClosureDatum f (f.fiberι (genericPoint (Spec (.of R))) y) hx
      (fiberDimension_pointClosure_eq f (genericPoint (Spec (.of R))) y hy).le) rfl⟩

/-- **Stacks Project, Lemma 0H5A.** Let `f : X ⟶ Spec R` be a morphism of finite type with `R` a
discrete valuation ring and let `r ≥ 0`. Then the cycle-class homomorphism of Equation 0H58 is
surjective: every relative `r`-cycle on `X/Spec R` is a combination of the classes `[Z/X/S]_r` of
members of `Hilb(X/Spec R, r)`.

A relative `r`-cycle is determined by its member over the generic point of `Spec R` by Tag 0H55,
and that member is the generic member of a cycle class by
`Stacks.Chow.exists_cycleClassMap_apply_genericPoint_eq`. -/
@[stacks 0H5A "finite type is the source's hypothesis, stated as locally of finite type plus \
quasi-compact"]
theorem surjective_relativeCycleClassMap {r : ℕ} {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    [QuasiCompact f] :
    Function.Surjective (relativeCycleClassMap (r := r) f) := by
  intro α
  obtain ⟨β, hβ⟩ :=
    exists_cycleClassMap_apply_genericPoint_eq f r (α.1 (genericPoint (Spec (.of R))))
  refine ⟨β, Subtype.ext ?_⟩
  refine (IsRelativeCycle.eq_iff_eq_of_mem_genericPoints f r
    (relativeCycleClassMap (r := r) f β).2 α.2).mpr fun ζ hζ ↦ ?_
  rw [genericPoints_eq_singleton] at hζ
  rwa [Set.mem_singleton_iff.mp hζ, relativeCycleClassMap_val f β]

end Stacks.Chow

end
