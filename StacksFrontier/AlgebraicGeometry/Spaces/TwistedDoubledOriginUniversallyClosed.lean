module

public import Mathlib.RingTheory.LaurentSeries
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEtaleOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginValuativeLift
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.FiniteSeparable

/-!
# The Galois twist of the affine line with zero doubled over the affine line

Let `k'/k` be a degree two Galois extension and let `X` be the Galois twist of the affine line
with zero doubled, the algebraic space over `S = 𝔸¹_k` of Stacks 03FN. Stacks 03KI makes the
following assertions about its structure morphism `π : X ⟶ S`:

* `π` is quasi-compact;
* `π` is universally closed;
* after base change by `Spec k' ⟶ Spec k`, `π` is identified with the morphism from the affine
  line over `k'` with zero doubled to the affine line over `k'`, which is universally closed;
* `Spec k' ⟶ Spec k` is universally closed and surjective;
* the point of `X` above `0 ∈ 𝔸¹_k` is a monomorphism `Spec k' ⟶ X`;
* the square with corners `Spec k((x))`, `X`, `Spec k⟦x⟧`, `𝔸¹_k` admits no dotted arrow;
* so a finite separable extension of the fraction field is needed in the existence part of the
  valuative criterion.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.doubledProjOver`: the projection of the affine line
  over `k'` with zero doubled onto the affine line over `k'`.
* `AlgebraicGeometry.TwistedDoubledOrigin.formalDiskValuativeSquare`: the solid valuative square
  of `π` over the valuation ring `k⟦x⟧` displayed in the source.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.isQuasiCompact_quotientBaseMap`: `π` is quasi-compact.
* `AlgebraicGeometry.TwistedDoubledOrigin.universallyClosed_quotientBaseMap`: `π` is universally
  closed.
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_isIso_baseChangePresheaf_comp_doubledProjOver`:
  the base change of `π` along `Spec k' ⟶ Spec k` is the affine line with zero doubled over
  the affine line over `k'`.
* `AlgebraicGeometry.TwistedDoubledOrigin.universallyClosed_doubledProjOver`: the affine line
  with zero doubled is universally closed over the affine line.
* `AlgebraicGeometry.TwistedDoubledOrigin.universallyClosed_surjective_specMap_algebraMap`:
  `Spec k' ⟶ Spec k` is universally closed and surjective.
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_mono_isPullback_zeroFibre`: the fibre of `π`
  over the origin is a monomorphism `Spec k' ⟶ X`.
* `AlgebraicGeometry.TwistedDoubledOrigin.isEmpty_lift_formalDiskValuativeSquare`: the square
  over `k⟦x⟧` has no dotted arrow.
* `AlgebraicGeometry.TwistedDoubledOrigin.existenceFiniteSeparable_and_not_forall_nonempty_lift`:
  `π` satisfies the existence part of the valuative criterion with finite separable extensions,
  but not without extending the fraction field.
* `AlgebraicGeometry.TwistedDoubledOrigin.quotientBaseMap_example`: **Stacks 03KI**, all the
  assertions of the example together.

## Implementation notes

*Quasi-compactness.* The quotient is quasi-compact as an algebraic space, its chart being the
affine line over `k'`. Part (1) of Stacks 073B turns that into quasi-compactness of a morphism
into any quasi-separated algebraic space, and the target here is `𝔸¹_k` read as a presheaf,
which is represented by an affine scheme.

*Universal closedness.* The source base changes by `Spec k' ⟶ Spec k` and pushes universal
closedness back down along that surjection. The proof here runs the same descent, Stacks 08AJ,
on the chart `U = Spec k'[x] ⟶ X` directly: it is surjective, and `U ⟶ S` is finite. The base
change identification of the source is proved separately, from the computation of part (6) of
Stacks 03FN: the base change of `X` along `U = S ×_{Spec k} Spec k' ⟶ S` is two copies of `U`
glued along the puncture, and the identification is compatible with the projections to `U`.

*The site.* All schemes are objects of a big fppf site `B` containing `S`. The formal disc
`Spec k⟦x⟧` and the field of Laurent series then belong to `B` as well, by Stacks 000R (9),
so the source's diagram needs no hypothesis on `B` beyond the one under which `X` is formed.

*The solid square and the missing arrow.* The top edge `Spec k((x)) ⟶ X` comes from the
isomorphism of Stacks 03FN away from the origin. Every point of `X` over the formal disc
restricts to a point over the origin, hence to a `k`-point of `Spec k'`, which does not exist:
this is `AlgebraicGeometry.TwistedDoubledOrigin.not_nonempty_hom_formalDisk`.

*The extension is needed.* `π` is quasi-separated (Stacks 03FN, part (5)) and universally closed,
so it satisfies the existence part of the valuative criterion (Stacks 0A3X), and by Stacks 03KH
with finite separable extensions of the fraction field; the square over `k⟦x⟧` shows that no
extension at all does not suffice.

## References

* [Stacks Project, Tag 03KI](https://stacks.math.columbia.edu/tag/03KI)
* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 03KH](https://stacks.math.columbia.edu/tag/03KH)
* [Stacks Project, Tag 0A3X](https://stacks.math.columbia.edu/tag/0A3X)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-! ### The extension of the ground field -/

/-- **Stacks 03KI, the morphism `Spec k' ⟶ Spec k`.** For a finite extension `k'/k` of fields,
the morphism `Spec k' ⟶ Spec k` is universally closed, being finite, and surjective, its
target being a single point. -/
@[stacks 03KI "Spec(k') → Spec(k) is universally closed and surjective"]
theorem universallyClosed_surjective_specMap_algebraMap [FiniteDimensional k K] :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨y⟩ : Nonempty (Spec (.of K)) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

/-! ### The site contains the formal disc -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k))

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over the base (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_TwistedDoubledOriginUniversallyClosed :
    HasPullbacks ((BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_TwistedDoubledOriginUniversallyClosed
    {X Y Z : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

include hS in
/-- The formal disc over `k` belongs to every big fppf site containing the affine line: the ring
`k⟦x⟧` has cardinality `#k ^ ℵ₀`, which is at most `size(𝔸¹_k) ^ ℵ₀`, so Stacks 000R (9)
applies. -/
theorem contains_powerSeries : B.Contains (Spec (.of (PowerSeries k))) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS ?_
  rw [Scheme.size_Spec]
  have hinj : Function.Injective (fun (f : PowerSeries k) (n : ℕ) => PowerSeries.coeff n f) :=
    fun f g h => PowerSeries.ext fun n => congrFun h n
  calc Cardinal.mk (PowerSeries k) ≤ Cardinal.mk (ℕ → k) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk k ^ Cardinal.aleph0 := by simp
    _ ≤ (max Cardinal.aleph0 (Cardinal.mk (Polynomial k))) ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_right
        ((Cardinal.mk_le_of_injective Polynomial.C_injective).trans (le_max_right _ _))

include hS in
/-- The field of Laurent series belongs to every big fppf site containing the affine line: it
is the fraction field of `k⟦x⟧`, hence a localization of it, and a localization of the ring of an
object of the site is again one by part (9)(c) of Stacks 000R. -/
theorem contains_laurentSeries : B.Contains (Spec (.of (LaurentSeries k))) :=
  Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (nonZeroDivisors (PowerSeries k)) (LaurentSeries k) (contains_powerSeries k B hS)

variable [FiniteDimensional k K] [IsGalois k K]

/-! ### The base, read as a presheaf -/

/-- The functor of points of the base over itself — the target of the structure morphism of the
quotient — is represented by the terminal object of the big fppf site over the base. -/
def pointsBaseOverBaseIso :
    Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k) ≅
      yoneda.obj (baseSiteObject k B hS) :=
  Space.pointsYonedaIso (Over.post B.inclusion) (baseSiteObject k B hS)

/-- The functor of points of the base over itself is a terminal presheaf. -/
def isTerminalPointsBaseOverBase :
    IsTerminal (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
      (baseOverBase k)) :=
  (Space.yonedaMkIdTerminal B (base k) hS).ofIso (pointsBaseOverBaseIso k B hS).symm

/-- The base, read as a presheaf, is an algebraic space over itself. -/
theorem isAlgebraicSpace_points_baseOverBase :
    IsAlgebraicSpace B (base k) hS
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k)) :=
  (isAlgebraicSpace_yoneda B (base k) hS (baseSiteObject k B hS)).of_iso
    (pointsBaseOverBaseIso k B hS).symm

/-- The base, read as a presheaf, is a quasi-separated algebraic space: it is represented by the
terminal object of the site, whose underlying scheme is the affine line, an affine scheme and so
a quasi-separated one. -/
theorem isAbsolutelyQuasiSeparated_points_baseOverBase :
    Space.IsAbsolutelyQuasiSeparated B (base k) hS B.contains_terminal
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k)) :=
  Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (base k) hS _
    B.contains_terminal
    ⟨baseSiteObject k B hS, (by change QuasiSeparatedSpace (base k); infer_instance),
      ⟨Functor.representableByEquiv.symm (pointsBaseOverBaseIso k B hS).symm⟩⟩

/-! ### Quasi-compactness of the structure morphism -/

variable (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
  [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)]

/-- **Stacks 03KI, the quasi-compactness clause.** The structure morphism `π : X ⟶ S = 𝔸¹_k` of
the Galois twist of the affine line with zero doubled is quasi-compact.

The quotient is a quasi-compact algebraic space, its chart being the affine line over `k'`, and
the base is quasi-separated, being affine; so part (1) of Stacks 073B applies. -/
@[stacks 03KI "π is quasi-compact"]
theorem isQuasiCompact_quotientBaseMap :
    Space.IsQuasiCompact B (base k) hS (quotientBaseMap k K hdegree σ hσ B hS) :=
  Space.isQuasiCompact_of_isQuasiCompactSpace B (base k) hS B.contains_terminal
    (isAlgebraicSpace_points_baseOverBase k B hS)
    (isAbsolutelyQuasiSeparated_points_baseOverBase k B hS)
    (isQuasiCompactSpace_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS) _

/-! ### Universal closedness of the structure morphism -/

/-- The chart `U = Spec k'[x] ⟶ X` of the twisted doubled origin, as a morphism of presheaves. -/
def quotientChart :
    yoneda.obj (coverSiteObject k K B hS) ⟶
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj :=
  yonedaEquiv.symm
    ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
      (Over.post B.inclusion) (twistedRelation k K σ)).app
      (Opposite.op (coverSiteObject k K B hS))
      (𝟙 ((Over.post B.inclusion).obj (coverSiteObject k K B hS))))

/-- The chart of the twisted doubled origin is surjective on points. -/
theorem isSurjective_quotientChart :
    Space.IsSurjective B (base k) hS (quotientChart k K B hS hdegree σ hσ) :=
  Space.isSurjective_of_presheafSurjective B (base k) hS _
    (surjective_toQuotientSheaf_twistedRelation k K hdegree σ hσ B hS)

/-- The structure morphism of the chart, as a morphism of the site into its terminal object. -/
def coverToBaseSiteObject : coverSiteObject k K B hS ⟶ baseSiteObject k B hS :=
  Over.homMk (coverSiteObject k K B hS).hom (by simp)

omit [IsGalois k K] in
/-- The chart is universally closed over the base: `k'[x]` is a finite `k[x]`-module, so the
morphism of affine lines is finite, hence integral, hence universally closed. -/
theorem universallyClosed_coverMap : UniversallyClosed (coverMap k K) :=
  have := isFinite_coverMap k K
  inferInstance

/-- The chart is universally closed over `X` and then over the base: the composite is the
structure morphism of the chart, which is universally closed. -/
theorem universallyClosed_quotientChart_comp :
    Space.UniversallyClosed B (base k) hS
      (quotientChart k K B hS hdegree σ hσ ≫ quotientBaseMap k K hdegree σ hσ B hS) := by
  set P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (base k) hS)
  have hPresp : P.presheaf.RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) P).respectsIso
  have hyon : P.presheaf (yoneda.map (coverToBaseSiteObject k K B hS)) :=
    (Space.presheaf_yoneda_map_iff B (base k) hS
      AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
      (coverToBaseSiteObject k K B hS)).mpr (universallyClosed_coverMap k K)
  have hcomp : P.presheaf ((quotientChart k K B hS hdegree σ hσ ≫
      quotientBaseMap k K hdegree σ hσ B hS) ≫ (pointsBaseOverBaseIso k B hS).hom) := by
    rw [show (quotientChart k K B hS hdegree σ hσ ≫ quotientBaseMap k K hdegree σ hσ B hS) ≫
        (pointsBaseOverBaseIso k B hS).hom = yoneda.map (coverToBaseSiteObject k K B hS) from
      (Space.yonedaMkIdTerminal B (base k) hS).hom_ext _ _]
    exact hyon
  have hpre : P.presheaf (quotientChart k K B hS hdegree σ hσ ≫
      quotientBaseMap k K hdegree σ hσ B hS) :=
    (MorphismProperty.cancel_right_of_respectsIso P.presheaf _
      (pointsBaseOverBaseIso k B hS).hom).1 hcomp
  exact Space.universallyClosed_of_presheaf_universallyClosed B (base k) hS
    (isAlgebraicSpace_yoneda B (base k) hS (coverSiteObject k K B hS))
    (isAlgebraicSpace_points_baseOverBase k B hS) hpre.rep hpre

/-- **Stacks 03KI, the universal closedness clause.** The structure morphism
`π : X ⟶ S = 𝔸¹_k` of the Galois twist of the affine line with zero doubled is universally
closed.

The chart `U = Spec k'[x] ⟶ X` is surjective and `U ⟶ S` is universally closed, being finite, so
Stacks 08AJ pushes universal closedness down to `π`. -/
@[stacks 03KI "π is universally closed"]
theorem universallyClosed_quotientBaseMap :
    Space.UniversallyClosed B (base k) hS (quotientBaseMap k K hdegree σ hσ B hS) :=
  Space.universallyClosed_of_isSurjective_comp B (base k) hS
    (isAlgebraicSpace_yoneda B (base k) hS (coverSiteObject k K B hS))
    (isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS)
    (isAlgebraicSpace_points_baseOverBase k B hS) _ _
    (universallyClosed_quotientChart_comp k K B hS hdegree σ hσ)
    (isSurjective_quotientChart k K B hS hdegree σ hσ)

/-! ### The base change to `k'` -/

/-- The projection of the affine line over `k'` with zero doubled onto the affine line over
`k'`, as a morphism of schemes over the base. -/
@[ega "I 5.5.11"]
def doubledProjOver : doubledOverBase k K ⟶ coverOverBase k K :=
  Over.homMk (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj rfl

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **Stacks 03KI, the affine line with zero doubled.** The affine line over `k'` with zero
doubled is universally closed over the affine line over `k'`.

The two copies of the affine line cover it, and their union maps to the affine line by the
codiagonal, which is finite; so Mathlib's descent of universal closedness along a surjection
applies. -/
@[stacks 03KI "the affine line with zero doubled is universally closed over the affine line"]
theorem universallyClosed_doubledProjOver : UniversallyClosed (doubledProjOver k K).left := by
  have : Surjective (doubledChartsToGlued k K) := (doubledChartsToGlued_fppf k K).2.2
  have : UniversallyClosed (doubledChartsToGlued k K ≫ (doubledProjOver k K).left) := by
    show UniversallyClosed (doubledChartsToGlued k K ≫
      (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj)
    rw [doubledChartsToGlued_comp_proj]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (doubledChartsToGlued k K) _

/-- The comparison map from the self-product of the chart to the affine line with zero doubled
lies over the first projection to the chart. -/
theorem doubledSelfProductToGlued_comp_doubledProjOver :
    doubledSelfProductToGlued k K hdegree σ hσ ≫ doubledProjOver k K =
      prod.fst (X := coverOverBase k K) (Y := coverOverBase k K) := by
  ext1
  rw [Over.comp_left, doubledSelfProductToGlued_left]
  show (coverSelfProductIso k K hdegree σ hσ).hom ≫ doubledChartsToGlued k K ≫
      (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj = _
  rw [doubledChartsToGlued_comp_proj, coverSelfProductIso, Iso.trans_hom, Category.assoc,
    ← coverFiberProductSplitIso_inv_fst k K hdegree σ hσ, Iso.hom_inv_id_assoc]
  exact Over.prodLeftIsoPullback_hom_fst _ _

/-- **Stacks 03KI, the base change to `k'`.** After base change along
`U = S ×_{Spec k} Spec k' = 𝔸¹_{k'} ⟶ S`, the structure morphism `π` is identified with the
morphism from the affine line over `k'` with zero doubled to the affine line over `k'`: the base
change `U ×_S X` is isomorphic to the functor of points of the glued scheme, compatibly with the
projections to `U`.

The isomorphism is the one of part (6) of Stacks 03FN; both it and the projections are
determined on the self-product `U ×_S U`, where both projections are the first one. -/
@[stacks 03KI "after base change by Spec(k') → Spec(k), π is the affine line with zero \
doubled over the affine line"]
theorem exists_isIso_baseChangePresheaf_comp_doubledProjOver :
    ∃ χ : baseChangePresheaf k K B hS hdegree σ hσ ⟶
        (pointsFunctor k B hS).obj (doubledOverBase k K),
      IsIso χ ∧ χ ≫ (pointsFunctor k B hS).map (doubledProjOver k K) =
        pullback.fst (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS) := by
  -- the comparison map to the functor of points of the glued scheme is locally bijective
  obtain ⟨hflat, hfp, hsurj⟩ := doubledChartsToGlued_fppf k K
  obtain ⟨_, _, _⟩ : Flat (doubledSelfProductToGlued k K hdegree σ hσ).left ∧
      LocallyOfFinitePresentation (doubledSelfProductToGlued k K hdegree σ hσ).left ∧
      Surjective (doubledSelfProductToGlued k K hdegree σ hσ).left := by
    rw [doubledSelfProductToGlued_left]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have _hR : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      ((pointsFunctor k B hS).map
        (pullback.lift (doubledRelation k K σ).target (doubledRelation k K σ).source
          (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))) := by
    have := isIso_pullbackLift_doubledRelation k K hdegree σ hσ
    infer_instance
  have _hU := isLocallySurjective_points_map_of_fppf B (base k) hS
    (doubledSelfProductToGlued k K hdegree σ hσ)
  have _hMinj := Stacks.Groupoids.quotientPresheafToPoints_isLocallyInjective
    (BigFppfOver.topology B (base k) hS) (Over.post (X := B.obj hS) B.inclusion)
    (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
    (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ) _hR
  have _hMsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      (Stacks.Groupoids.quotientPresheafToPoints (Over.post (X := B.obj hS) B.inclusion)
        (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
        (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (Stacks.Groupoids.toQuotientPresheaf_comp_quotientPresheafToPoints
        (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ)
        (doubledSelfProductToGlued k K hdegree σ hσ)
        (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))
  -- the comparison map to the base change is locally bijective
  have _hBsurj := isLocallySurjective_quotientToBaseChange k K B hS hdegree σ hσ
  have _hBinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B (base k) hS)
      (quotientToBaseChange k K B hS hdegree σ hσ) :=
    Presheaf.isLocallyInjective_of_injective _ _
      (injective_quotientToBaseChange k K B hS hdegree σ hσ)
  obtain ⟨χ, hχ, -⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective
    (BigFppfOver.topology B (base k) hS) (quotientToBaseChange k K B hS hdegree σ hσ)
    (Stacks.Groupoids.quotientPresheafToPoints (Over.post (X := B.obj hS) B.inclusion)
      (doubledRelation k K σ) (doubledSelfProductToGlued k K hdegree σ hσ)
      (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (doubledOverBase k K))
  refine ⟨χ, Presheaf.isIso_of_isLocallyBijective_fac _ _ _
    (isSheaf_baseChangePresheaf k K B hS hdegree σ hσ)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (doubledOverBase k K)) hχ, ?_⟩
  -- compatibility with the projections, checked after the locally bijective comparison map
  obtain ⟨_, -, huniq⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective
    (BigFppfOver.topology B (base k) hS) (quotientToBaseChange k K B hS hdegree σ hσ)
    (quotientToBaseChange k K B hS hdegree σ hσ ≫
      pullback.fst (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS))
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS
      (coverOverBase k K))
  refine (huniq _ ?_).trans (huniq _ rfl).symm
  dsimp only
  rw [← Category.assoc, hχ]
  refine (cancel_epi (Stacks.Groupoids.toQuotientPresheaf
    (Over.post (X := B.obj hS) B.inclusion) (doubledRelation k K σ))).1 ?_
  rw [← Category.assoc, ← Category.assoc,
    Stacks.Groupoids.toQuotientPresheaf_comp_quotientPresheafToPoints,
    toQuotientPresheaf_comp_quotientToBaseChange, coverSelfProductToBaseChange_comp_fst]
  show (pointsFunctor k B hS).map _ ≫ (pointsFunctor k B hS).map _ = _
  rw [← Functor.map_comp, doubledSelfProductToGlued_comp_doubledProjOver]

/-! ### The fibre over the origin -/

/-- The origin of the base, as a morphism of schemes over the base. -/
def zeroBaseToBase : zeroBaseOverBase k ⟶ baseOverBase k :=
  Over.homMk (zeroBaseOverBase k).hom (by simp)

/-- The origin of the chart lies over the origin of the base, by `Spec k' ⟶ Spec k`. -/
def zeroCoverToZeroBase : zeroCoverOverBase k K ⟶ zeroBaseOverBase k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) (by
    dsimp [zeroBaseOverBase, zeroCoverOverBase]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply Polynomial.ringHom_ext <;> intros <;> simp)

/-- The origin of the base is a monomorphism over the base, being a closed immersion. -/
instance mono_zeroBaseToBase : Mono (zeroBaseToBase k) := by
  have : IsClosedImmersion (zeroBaseToBase k).left :=
    IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩
  exact Over.mono_of_mono_left _

/-- **Stacks 03KI, the point above the origin.** The point of `X` above `0 ∈ 𝔸¹_k` is a
monomorphism `Spec k' ⟶ X`: there is a monomorphism from the functor of points of `Spec k'`
into `X` whose square over the origin `Spec k ⟶ 𝔸¹_k` is Cartesian, so `Spec k'` is the whole
fibre of `π` over the origin.

The fibre is computed in
`AlgebraicGeometry.TwistedDoubledOrigin.twistedRelationQuotient_zeroFibre`; its map to `X` is a
monomorphism because the origin is a monomorphism into the base. -/
@[stacks 03KI "the point of X above 0 corresponds to a monomorphism Spec(k') → X"]
theorem exists_mono_isPullback_zeroFibre :
    ∃ m : (pointsFunctor k B hS).obj (zeroCoverOverBase k K) ⟶
        (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj,
      Mono m ∧ IsPullback m ((pointsFunctor k B hS).map (zeroCoverToZeroBase k K))
        (quotientBaseMap k K hdegree σ hσ B hS)
        ((pointsFunctor k B hS).map (zeroBaseToBase k)) := by
  let Q := (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj
  let Z := (pointsFunctor k B hS).obj (zeroBaseOverBase k)
  let e : (Q ⨯ Z) ≅ (pointsFunctor k B hS).obj (zeroCoverOverBase k K) :=
    Classical.choice (twistedRelationQuotient_zeroFibre (k := k) (K := K) σ B hS)
  have hT := isTerminalPointsBaseOverBase k B hS
  have : Mono ((pointsFunctor k B hS).map (zeroBaseToBase k)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [mono_iff_injective]
    intro a b hab
    exact (cancel_mono (zeroBaseToBase k)).1 hab
  have hpb : IsPullback (e.inv ≫ prod.fst) ((pointsFunctor k B hS).map (zeroCoverToZeroBase k K))
      (quotientBaseMap k K hdegree σ hσ B hS) ((pointsFunctor k B hS).map (zeroBaseToBase k)) :=
    (IsPullback.of_is_product (prodIsProd Q Z) hT).of_iso e (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp)
      ((cancel_mono ((pointsFunctor k B hS).map (zeroBaseToBase k))).1 (hT.hom_ext _ _))
      (hT.hom_ext _ _) (hT.hom_ext _ _)
  exact ⟨_, hpb.mono_fst_of_mono, hpb⟩

/-! ### The solid valuative square over the formal disc -/

/-- The generic point of the formal disc, read over the affine line: the coordinate of the line
goes to the power-series variable, taken in the field of Laurent series. -/
abbrev laurentBaseMap : Spec (.of (LaurentSeries k)) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫
    formalDiskBaseMap k

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The generic point of the formal disc misses the origin of the base: the coordinate pulls back
to the power-series variable, which is a nonzero element of a field and so invertible. -/
theorem laurentBaseMap_preimage_puncturedBase :
    (laurentBaseMap k) ⁻¹ᵁ puncturedBase k = ⊤ := by
  have h : laurentBaseMap k = Spec.map (CommRingCat.ofHom
      ((algebraMap (PowerSeries k) (LaurentSeries k)).comp
        (Polynomial.eval₂RingHom (algebraMap k (PowerSeries k)) PowerSeries.X))) := by
    rw [laurentBaseMap, formalDiskBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [h, SpecMap_preimage_basicOpen]
  exact eq_top_iff.2 fun p _ hmem =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (by simp))

/-- The generic point of the formal disc, factored through the punctured base. -/
def laurentPuncturedFactor : Spec (.of (LaurentSeries k)) ⟶ (puncturedBase k).toScheme :=
  (Spec (.of (LaurentSeries k))).topIso.inv ≫
    (laurentBaseMap k).resLE (puncturedBase k) ⊤
      (laurentBaseMap_preimage_puncturedBase k).ge

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The factorization of the generic point of the formal disc through the punctured base,
followed by the inclusion of the punctured base, is the generic point of the formal disc. -/
@[simp]
theorem laurentPuncturedFactor_ι :
    laurentPuncturedFactor k ≫ (puncturedBase k).ι = laurentBaseMap k := by
  simp [laurentPuncturedFactor, Scheme.Hom.resLE_comp_ι]

/-- The section of the structure morphism of the quotient over the punctured base: away from the
origin `π` is an isomorphism by Stacks 03FN, and this is its inverse. -/
def puncturedSection :
    Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (puncturedBaseOverBase k) ⟶
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj :=
  have := isIso_quadraticGaloisTwistedDoubledOrigin_over_puncturedBase k K hdegree σ hσ B hS
  inv (pullback.snd (quotientBaseMap k K hdegree σ hσ B hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (puncturedBaseInclusion k)))) ≫ pullback.fst _ _

/-- The point of the Galois twist over `Spec k((x))`, the top edge of the square displayed in
Stacks 03KI: the generic point of the formal disc lands in the punctured base, where the quotient
agrees with the base. -/
def laurentGenericPoint :
    yoneda.obj (siteObject B (base k) hS (contains_laurentSeries k B hS)
        (laurentBaseMap k)) ⟶
      (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj :=
  yonedaEquiv.symm (show (Over.post (X := B.obj hS) B.inclusion).obj
      (siteObject B (base k) hS (contains_laurentSeries k B hS) (laurentBaseMap k)) ⟶
        puncturedBaseOverBase k from
      Over.homMk (laurentPuncturedFactor k)
        (show laurentPuncturedFactor k ≫ (puncturedBase k).ι = laurentBaseMap k from
          laurentPuncturedFactor_ι k)) ≫
    puncturedSection k K B hS hdegree σ hσ

/-- **Stacks 03KI, the solid square.** The square displayed in the example: its valuation ring is
the ring `k⟦x⟧` of formal power series, its fraction field the field `k((x))` of Laurent series,
its structure morphism over the base the coordinate map `Spec k⟦x⟧ ⟶ 𝔸¹_k` of
`AlgebraicGeometry.TwistedDoubledOrigin.formalDiskBaseMap`, and its top edge the point
`Spec k((x)) ⟶ X` of
`AlgebraicGeometry.TwistedDoubledOrigin.laurentGenericPoint`.

Only the top edge carries content: the target of `π` is the terminal presheaf, so the edge of the
square into it, and the commutativity of the square, are the only ones there are. -/
@[stacks 03KI "the solid square of the displayed diagram, over the valuation ring k⟦x⟧"]
def formalDiskValuativeSquare :
    Space.ValuativeSquare (quotientBaseMap k K hdegree σ hσ B hS) where
  R := PowerSeries k
  K := LaurentSeries k
  ring_mem := contains_powerSeries k B hS
  field_mem := contains_laurentSeries k B hS
  base := formalDiskBaseMap k
  generic := laurentGenericPoint k K B hS hdegree σ hσ
  special := yonedaEquiv.symm ((Over.mkIdTerminal (X := base k)).from _)
  comm := by
    ext T x
    exact (Over.mkIdTerminal (X := base k)).hom_ext _ _

/-- **Stacks 03KI, the missing dotted arrow.** The square of the example has no dotted arrow: a
dotted arrow is in particular a point of the quotient over the formal disc, and there is none,
the point of `X` above the origin being `Spec k'`, which has no `k`-point. -/
@[stacks 03KI "there cannot exist a dotted arrow"]
theorem isEmpty_lift_formalDiskValuativeSquare :
    IsEmpty (formalDiskValuativeSquare k K B hS hdegree σ hσ).Lift :=
  ⟨fun l => not_nonempty_hom_formalDisk k K hdegree σ hσ B hS (contains_powerSeries k B hS)
    ⟨l.map⟩⟩

/-- **Stacks 03KI, a finite separable extension is needed.** The structure morphism `π` satisfies
the existence part of the valuative criterion when the fraction field may be replaced by a
finite separable extension, but not when it may not be extended at all.

The first half is Stacks 0A3X, part (1), for the quasi-separated (Stacks 03FN, part (5)) and
universally closed morphism `π`, refined by Stacks 03KH; the second is the square of the example
over `k⟦x⟧`. -/
@[stacks 03KI "a finite separable field extension is needed in general"]
theorem existenceFiniteSeparable_and_not_forall_nonempty_lift :
    Space.ExistenceFiniteSeparable (quotientBaseMap k K hdegree σ hσ B hS) ∧
      ¬ ∀ q : Space.ValuativeSquare (quotientBaseMap k K hdegree σ hσ B hS), Nonempty q.Lift := by
  have hX := isAlgebraicSpace_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS
  have hY := isAlgebraicSpace_points_baseOverBase k B hS
  exact ⟨(Space.valuativeCriterion_existence_iff_finiteSeparable B (base k) hS hX hY _).1
      (Space.valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed hX hY _
        (Space.isQuasiSeparated_of_isQuasiSeparatedOver B (base k) hS
          (isQuasiSeparatedOver_quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS) _)
        (universallyClosed_quotientBaseMap k K B hS hdegree σ hσ)),
    fun h => (isEmpty_lift_formalDiskValuativeSquare k K B hS hdegree σ hσ).false
      (h (formalDiskValuativeSquare k K B hS hdegree σ hσ)).some⟩

/-! ### The example -/

/-- **Stacks 03KI.** Let `k'/k` be a degree two Galois extension and let `X` be the Galois twist
of the affine line with zero doubled, the algebraic space of Stacks 03FN over `S = 𝔸¹_k`, with
structure morphism `π : X ⟶ S`. Then:

* `π` is quasi-compact and universally closed;
* after base change along `𝔸¹_{k'} = S ×_{Spec k} Spec k' ⟶ S`, `π` is identified with the
  affine line over `k'` with zero doubled over the affine line over `k'`, which is universally
  closed;
* `Spec k' ⟶ Spec k` is universally closed and surjective;
* the point of `X` above the origin is a monomorphism `Spec k' ⟶ X`, the whole fibre of `π`
  there;
* the formal disc `Spec k⟦x⟧` over `S` carries no point of `X`, so the square of the example
  (`AlgebraicGeometry.TwistedDoubledOrigin.formalDiskValuativeSquare`) has no dotted arrow;
* `π` satisfies the existence part of the valuative criterion with finite separable extensions
  of the fraction field, but not without extending it. -/
@[stacks 03KI "all the assertions of the example together"]
theorem quotientBaseMap_example :
    Space.IsQuasiCompact B (base k) hS (quotientBaseMap k K hdegree σ hσ B hS) ∧
      Space.UniversallyClosed B (base k) hS (quotientBaseMap k K hdegree σ hσ B hS) ∧
      (∃ χ : baseChangePresheaf k K B hS hdegree σ hσ ⟶
          (pointsFunctor k B hS).obj (doubledOverBase k K),
        IsIso χ ∧ χ ≫ (pointsFunctor k B hS).map (doubledProjOver k K) =
          pullback.fst (pointsCoverToBase k K B hS) (quotientBaseMap k K hdegree σ hσ B hS)) ∧
      UniversallyClosed (doubledProjOver k K).left ∧
      (UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      (∃ m : (pointsFunctor k B hS).obj (zeroCoverOverBase k K) ⟶
          (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj,
        Mono m ∧ IsPullback m ((pointsFunctor k B hS).map (zeroCoverToZeroBase k K))
          (quotientBaseMap k K hdegree σ hσ B hS)
          ((pointsFunctor k B hS).map (zeroBaseToBase k))) ∧
      ¬ Nonempty
        (yoneda.obj (siteObject B (base k) hS (contains_powerSeries k B hS)
            (formalDiskBaseMap k)) ⟶
          (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj) ∧
      IsEmpty (formalDiskValuativeSquare k K B hS hdegree σ hσ).Lift ∧
      Space.ExistenceFiniteSeparable (quotientBaseMap k K hdegree σ hσ B hS) ∧
      ¬ ∀ q : Space.ValuativeSquare (quotientBaseMap k K hdegree σ hσ B hS), Nonempty q.Lift :=
  ⟨isQuasiCompact_quotientBaseMap k K B hS hdegree σ hσ,
    universallyClosed_quotientBaseMap k K B hS hdegree σ hσ,
    exists_isIso_baseChangePresheaf_comp_doubledProjOver k K B hS hdegree σ hσ,
    universallyClosed_doubledProjOver k K,
    universallyClosed_surjective_specMap_algebraMap k K,
    exists_mono_isPullback_zeroFibre k K B hS hdegree σ hσ,
    not_nonempty_hom_formalDisk k K hdegree σ hσ B hS (contains_powerSeries k B hS),
    isEmpty_lift_formalDiskValuativeSquare k K B hS hdegree σ hσ,
    existenceFiniteSeparable_and_not_forall_nonempty_lift k K B hS hdegree σ hσ⟩

end AlgebraicGeometry.TwistedDoubledOrigin

end
