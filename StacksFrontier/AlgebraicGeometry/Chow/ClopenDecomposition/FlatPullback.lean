module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection onto an open piece is flat pullback

The source describes the projections of the product decomposition
`Z_k(X) = \prod_i Z_k(X_i)` of Stacks 0FDZ and Stacks 02UC as *flat pullback* along the open
immersion `X_i → X`: "the projection maps `CH_{k-p}(X'') → CH_{k-p}(X'_i)` are given by flat
pullback". This file proves that, identifying `Stacks.Chow.cycleGroupOpensRestrict` — the
projection as defined, by restricting the coefficient function — with
`Stacks.Chow.flatPullback` along `U.ι`, which is flat and locally of finite type of relative
dimension zero.

The content is a multiplicity computation. The flat pullback of a cycle has, at a point `z` of
`U`, the coefficient of the cycle at the image of `z` times the multiplicity of `z` in the
scheme-theoretic inverse image of the reduced closure of that image. That inverse image is
computed by `Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`: pulling the reduced
closure of `j z` back along an open immersion `j` gives the reduced closure of `z`, because the
inverse image is reduced (being an open subscheme of a reduced scheme) and has the right support,
and a reduced closed subscheme is determined by its support — the uniqueness half of Stacks 01J3.
The multiplicity of an integral closed subscheme at its own generic point is one, which is
Stacks 02QU.

## Main results

* `Stacks.Chow.relativeDimension_opensι` — **Stacks 02NJ**: the inclusion of an open subscheme has
  relative dimension zero, so flat pullback along it is defined in degree `k ↦ k`.
* `Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion` — the inverse image along an open
  immersion of the reduced closure of a point is the reduced closure of the point.
* `Stacks.Chow.flatPullbackWeight_opensι` — a point of an open subscheme occurs with multiplicity
  one in the inverse image of the reduced closure of its image.
* `Stacks.Chow.flatPullback_opensι` — **Stacks 02UC**'s description of the projection: flat
  pullback along the inclusion of an open subscheme restricts the coefficient function.
* `Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback` — the same, read as an identity of
  homomorphisms of cycle groups.

## Implementation notes

`Stacks.Chow.flatPullback` along `U.ι` lands in degree `k + ((0 : ℕ) : ℤ)` rather than `k`, so the
two homomorphisms do not literally have the same type. The results below are therefore stated on
the underlying coefficient functions, where the degree index does not appear, and
`Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback` carries the degree transport explicitly as
an equality of the `.1` components.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02NJ.** The inclusion of an open subscheme has relative dimension zero: it is an open
immersion, hence locally quasi-finite. This is the hypothesis that
`Stacks.Chow.flatPullback` along `U.ι` takes. -/
theorem relativeDimension_opensι {X : Scheme.{u}} (U : X.Opens) :
    AlgebraicGeometry.RelativeDimension U.ι 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance

/-- The inverse image along an open immersion `j : U ⟶ X` of the reduced closure of `j z` is the
reduced closure of `z`.

The inverse image is the categorical pullback `U ×_X W`, which is an open subscheme of the reduced
scheme `W`, hence reduced; its support is the preimage of the closure of `j z`, which is the
closure of `z` because `j` is an open embedding. A reduced closed subscheme is determined by its
support, which is the uniqueness half of Stacks 01J3. -/
@[ega "I 5.2.3" "special case"]
theorem comap_integralComponentAt_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (z : U) :
    (integralComponentAt (j.base z)).comap j = integralComponentAt z := by
  set I : U.IdealSheafData := integralComponentAt z with hI
  set J : X.IdealSheafData := integralComponentAt (j.base z) with hJ
  set p : pullback j J.subschemeι ⟶ U := pullback.fst j J.subschemeι with hp
  have hqopen : IsOpenImmersion (pullback.snd j J.subschemeι) := inferInstance
  have hpclosed : IsClosedImmersion p := inferInstance
  have hpre : j.base ⁻¹' closure ({j.base z} : Set X) = closure ({z} : Set U) := by
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
    congr 1
    ext y
    simp [j.isOpenEmbedding.injective.eq_iff]
  have hker : p.ker = J.comap j := by
    simpa [hp] using (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion J.subschemeι j)
  have hsupp : p.ker.support = I.support := by
    rw [hker, Scheme.IdealSheafData.support_comap]
    apply SetLike.coe_injective
    simpa [hI, hJ, integralComponentAt, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] using hpre
  have hJred : IsReduced J.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hpullred : IsReduced (pullback j J.subschemeι) :=
    isReduced_of_isOpenImmersion (pullback.snd j J.subschemeι)
  have hkeq : p.ker = (p.ker.subschemeι).ker := by simp
  have hliftiso : IsIso (IsClosedImmersion.lift p p.ker.subschemeι hkeq.le) :=
    IsClosedImmersion.isIso_lift p p.ker.subschemeι hkeq
  have hkerred : IsReduced p.ker.subscheme :=
    isReduced_of_isOpenImmersion (asIso (IsClosedImmersion.lift p p.ker.subschemeι hkeq.le)).hom
  have hIred : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hIeq : p.ker = I :=
    (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme p.ker I.support hsupp).trans
      (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl).symm
  exact hker.symm.trans hIeq

/-- **Stacks 02QU.** A point of an open subscheme `U ⊆ X` occurs with multiplicity one in the
scheme-theoretic inverse image of the reduced closure of its image: that inverse image is the
reduced closure of the point itself, which is integral, and an integral closed subscheme has
multiplicity one at its generic point. -/
theorem flatPullbackWeight_opensι (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens) (j : ℤ) (z : (U : Scheme.{u}))
    (hz : relativeDimension C.dimensionFunction f (U.ι.base z) = j) :
    flatPullbackWeight C (U.ι ≫ f) U.ι j z = 1 := by
  have hcomap := comap_integralComponentAt_of_isOpenImmersion U.ι z
  have hint : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have hmem : genericPoint (integralComponentAt z).subscheme ∈
      genericPoints (integralComponentAt z).subscheme :=
    genericPoint_mem_genericPoints _
  have hgen : (integralComponentAt z).subschemeι.base
      (genericPoint (integralComponentAt z).subscheme) = z :=
    genericPointOf_integralComponentAt z
  have hdim : relativeDimension C.dimensionFunction (U.ι ≫ f)
      ((integralComponentAt z).subschemeι.base
        (genericPoint (integralComponentAt z).subscheme)) = j := by
    rw [hgen, relativeDimension_opensι_comp]
    exact hz
  have hkey : (cycleAssociatedToClosedSubscheme C (U.ι ≫ f)
      (integralComponentAt z).subschemeι j).1 z = 1 := by
    have h := cycleAssociatedToClosedSubscheme_apply C (U.ι ≫ f)
      (integralComponentAt z).subschemeι j ⟨_, hmem⟩ hdim
    rw [componentMultiplicity_eq_one (integralComponentAt z).subschemeι hmem] at h
    simpa only [hgen] using h
  have he := congrArg (fun K : (U : Scheme.{u}).IdealSheafData ↦
    (cycleAssociatedToClosedSubscheme C (U.ι ≫ f) K.subschemeι j).1 z) hcomap
  show (cycleAssociatedToClosedSubscheme C (U.ι ≫ f)
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({U.ι.base z} : Set X))).comap U.ι).subschemeι j).1 z = 1
  exact he.trans hkey

/-- **Stacks 02UC.** Flat pullback along the inclusion of an open subscheme is the restriction of
the coefficient function: this is the source's description of the projections of the product
decomposition `Z_k(X) = ∏_i Z_k(X_i)` as flat pullbacks. -/
theorem flatPullback_opensι (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens)
    (hr : AlgebraicGeometry.RelativeDimension U.ι 0) (k : ℤ) (α : CycleGroup C f k) :
    (flatPullback C (U.ι ≫ f) f U.ι rfl 0 hr k α).1 = opensRestrictCycle U α.1 := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [flatPullback_apply, opensRestrictCycle_apply]
  by_cases hα : α.1 (U.ι.base z) = 0
  · rw [hα, zero_mul]
  · have hdim : relativeDimension C.dimensionFunction f (U.ι.base z) = k :=
      (mem_cyclesOfDimension_iff_forall_point C f k α.1).mp α.2 _ hα
    rw [flatPullbackWeight_opensι C f U (k + ((0 : ℕ) : ℤ)) z (by rw [hdim]; simp), mul_one]

/-- **Stacks 02UC.** The projection `Stacks.Chow.cycleGroupOpensRestrict` onto the cycles of an
open subscheme is flat pullback along the inclusion of that subscheme, as a map of cycle
groups. -/
theorem cycleGroupOpensRestrict_eq_flatPullback (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (U : X.Opens)
    (hr : AlgebraicGeometry.RelativeDimension U.ι 0) (k : ℤ) (α : CycleGroup C f k) :
    (cycleGroupOpensRestrict C f U k α).1 =
      (flatPullback C (U.ι ≫ f) f U.ι rfl 0 hr k α).1 :=
  (flatPullback_opensι C f U hr k α).symm

/-! ### Consequence for rational equivalence -/

/-- Being rationally equivalent to zero is carried along a transport of the degree. -/
theorem mem_rationalEquivalences_cast (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {k k' : ℤ} (h : k = k') {α : CycleGroup C p k}
    (hα : α ∈ rationalEquivalences C p k) :
    (h ▸ α : CycleGroup C p k') ∈ rationalEquivalences C p k' := by
  subst h
  exact hα

/-- **Restriction to an open subscheme preserves rational equivalence, given Stacks 02S1 along the
inclusion of that subscheme.**

Since the projection is flat pullback along `U.ι`, the assertion that it carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero *is* Stacks 02S1 for `U.ι`, which this
development carries as the hypothesis
`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence`. So the forward half of
`Stacks.Chow.RationalEquivalenceDecomposes` is not a new statement: it is that standing hypothesis,
instantiated at the inclusions of the pieces. -/
theorem cycleGroupOpensRestrict_mem_rationalEquivalences (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (U : X.Opens) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (U.ι ≫ f) f U.ι rfl 0
      (relativeDimension_opensι U) k)
    {c : CycleGroup C f k} (hc : c ∈ rationalEquivalences C f k) :
    cycleGroupOpensRestrict C f U k c ∈ rationalEquivalences C (U.ι ≫ f) k := by
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  have heq : (hk ▸ flatPullback C (U.ι ≫ f) f U.ι rfl 0 (relativeDimension_opensι U) k c :
      CycleGroup C (U.ι ≫ f) k) = cycleGroupOpensRestrict C f U k c := by
    refine Subtype.ext ?_
    rw [val_cycleGroup_cast C (U.ι ≫ f) hk]
    exact flatPullback_opensι C f U (relativeDimension_opensι U) k c
  rw [← heq]
  exact mem_rationalEquivalences_cast C (U.ι ≫ f) hk (hfac c hc)

end Stacks.Chow

end
