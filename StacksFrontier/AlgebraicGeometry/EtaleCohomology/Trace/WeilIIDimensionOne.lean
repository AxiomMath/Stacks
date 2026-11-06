module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SurjectiveClosedImmersionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveSheafBound

/-!
# The weight bound of Weil II in dimension one

The reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) to opens of the
affine line in dimension one: every nonempty scheme of dimension at most one separated of finite
type over a finite field `k` has a nonempty open subscheme whose reduction is finite étale over an
open `D(g)` of `𝔸¹_k` (`Stacks.GenericFiniteEtale.exists_finite_etale_specAway`), and the weight
bound passes

* from a scheme to the scheme it is a surjective closed subscheme of
  (`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_surjective`), and
* from a smooth curve `V` to a connected finite étale cover `π : U ⟶ V`
  (`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_finite_etale`): `Hⁱ_c(U_k̄, F)` is
  `Hⁱ_c(V_k̄, π_* F)` through a compactification of `U` finite over one of `V`
  (`AlgebraicGeometry.CoverCompactification`), and `π_* F` is lisse, pointwise mixed and
  realizable when `F` is.

On `D(g)` itself the weight bound is the curve case on opens of the affine line
(`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`) for lisse sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_weilIICurveBoundOpenAffineLine`).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_surjective`.
* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_finite_etale`.
* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_weilIICurveBoundOpenAffineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
  {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q} {ι : ℚ_[ℓ] →+* ℂ}

/-- **The weight bound along a surjective closed immersion**: if `Z ⟶ X` is a surjective closed
immersion (for instance the reduction of `X`), the weight bound on `Z` gives the weight bound on
`X`, given the finite dimensionality of the cohomology of `Z`. -/
theorem LAdicSheaf.satisfiesWeightBound_of_surjective {X : B.Scheme} [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {Z : B.Scheme} [IsNoetherian Z.1] (iZ : Z ⟶ X) [IsClosedImmersion (B.inclusion.map iZ)]
    (hsurj : Function.Surjective (B.inclusion.map iZ).base)
    (hfinZ : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Z (B.inclusion.map iZ ≫ f))
    (hZ : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι Z (B.inclusion.map iZ ≫ f)) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  intro j F w hl hm hr i _
  have hgZ : ∀ y : closedPoints Z.1, (B.inclusion.map iZ).base y.1 ∈ closedPoints X.1 :=
    mem_closedPoints_of_isClosedImmersion (B.inclusion.map iZ)
  have := (hfinZ (j.restrictClosed (B.inclusion.map iZ)) (LAdicSheaf.inverseImage iZ F) i).1
  exact isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_surjective
    B ℓ f j kbar p q hcard F i iZ hsurj
    (hZ (j.restrictClosed (B.inclusion.map iZ)) (LAdicSheaf.inverseImage iZ F) w
      (hl.inverseImage iZ) (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage X ℓ iZ f hm hgZ)
      (LAdicSheaf.IsIotaRealizable.inverseImage ℓ f iZ hr hgZ) i)

/-- **The weight bound along a finite étale cover of a smooth curve.**  Let `V` be a smooth curve
over `k` and `π : U ⟶ V` finite étale with `U` connected. The weight bound on `V` gives the
weight bound on `U`, since `π_*` preserves pointwise mixedness and realizability
(`Stacks.EtaleCohomology.LAdicSheaf.IsPointwiseMixedOfWeightLE.directImage`,
`Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable.directImage`): a smooth
projective compactification `Ū` of `U` with a finite `Ū ⟶ V̄` over a compactification `V̄` of `V`
(`AlgebraicGeometry.nonempty_coverCompactification`) identifies `Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ)` with
`Hⁱ_c(V_k̄, π_* F ⊗ ℚ_ℓ)`, Frobenius-equivariantly (in the namespace `LAdicSheaf`,
`isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_integral`),
and on the curve `U` one compactification suffices
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_isCurve`). -/
theorem LAdicSheaf.satisfiesWeightBound_of_finite_etale {U V : B.Scheme} [IsNoetherian U.1]
    [IsNoetherian V.1] [ConnectedSpace U.1] (fV : V.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV]
    [QuasiCompact fV] [IsSeparated fV] [IsCurve k fV] [Smooth fV] (π : U ⟶ V)
    [IsFinite (B.inclusion.map π)] [Etale (B.inclusion.map π)]
    [LocallyOfFiniteType (B.inclusion.map π ≫ fV)] [QuasiCompact (B.inclusion.map π ≫ fV)]
    [IsSeparated (B.inclusion.map π ≫ fV)] (jV : CompactificationOf (Over.mk fV))
    (hfin : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar U (B.inclusion.map π ≫ fV))
    (hV : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι V fV) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U (B.inclusion.map π ≫ fV) := by
  set π' := B.inclusion.map π
  have hjV := CompactificationOf.immersion_toBase jV
  have : ConnectedSpace (B.inclusion.obj U) := ‹ConnectedSpace U.1›
  let C := (nonempty_coverCompactification k fV jV.toBase jV.immersion hjV π').some
  have hW : C.j ≫ C.q = π' ≫ fV := C.j_comp_q fV hjV
  let j₀ : CompactificationOf (Over.mk (π' ≫ fV)) :=
    ⟨StructuredArrow.mk (Y := Over.mk C.q)
      (Over.homMk (U := Over.mk (π' ≫ fV)) (V := Over.mk C.q) C.j hW),
      ⟨C.isOpenImmersion, C.isProper⟩⟩
  have : IsCurve k (π' ≫ fV) := isCurve_comp_of_isFinite_of_etale k fV π'
  refine LAdicSheaf.satisfiesWeightBound_of_isCurve U (π' ≫ fV) j₀ hfin
    fun F w hl hm hr i _ => ?_
  have hF := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse F hl
  let G := AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage π F hF
  let e := LAdicSheaf.padicTowerFiniteEtaleDirectImageIso ℓ π F hF
  have sq : IsPullback π' j₀.immersion jV.immersion C.fb := C.isPullback.flip
  have : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ fV jV kbar G i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral B ℓ
      (π' ≫ fV) j₀ fV jV π' C.fb C.hq sq kbar F G e i
  exact (isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_integral
    B ℓ (π' ≫ fV) j₀ fV jV π' C.fb C.hq sq kbar F G e p q hcard i).1
    (hV jV G w (AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage_isLisse π F hF)
      (LAdicSheaf.IsPointwiseMixedOfWeightLE.directImage π F hF fV hm)
      (LAdicSheaf.IsIotaRealizable.directImage π F hF fV hr) i)

/-- **The weight bound for lisse sheaves on an affine open of the affine line**, from the curve
case of Weil II on such opens (`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`) and the
correspondence between lisse sheaves and representations. -/
theorem LAdicSheaf.satisfiesWeightBound_of_weilIICurveBoundOpenAffineLine
    (hcurve : WeilIICurveBoundOpenAffineLine.{u}) (U : B.Scheme) [IsNoetherian U.1]
    [ConnectedSpace U.1] (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] [IsAffine U.1]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (hℓ : ℓ ≠ p) (x : GeometricPoint U.1) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U f :=
  LAdicSheaf.satisfiesWeightBound_of_forall_representationSheaf U f x
    fun j _ ρ hρ w hm hr i _ => hcurve B U ℓ k f e he j kbar p q hcard hℓ x ρ hρ ι w hm hr i

end Stacks.EtaleCohomology
