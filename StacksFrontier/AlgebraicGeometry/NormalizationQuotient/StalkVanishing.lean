module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Vanishing
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# The normalization quotient is supported on the singular locus

Let `X` be a reduced Nagata scheme of dimension one and let `ν : X^ν ⟶ X` be its normalization.
This file proves that the stalk of `ν_* 𝒪_{X^ν} / 𝒪_X` at a point vanishes exactly when that
point is regular, which is the pointwise half of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2).

The argument is entirely local.  Taking the stalk at `x` is exact, so the stalk of the cokernel
vanishes exactly when the stalk of `𝒪_X ⟶ ν_* 𝒪_{X^ν}` is an epimorphism, which is surjectivity
of `𝒪_{X,x} ⟶ (ν_* 𝒪_{X^ν})_x`.  By Tag 0C3B(2) the target is the integral closure of `𝒪_{X,x}`
in its total ring of fractions, so that surjectivity says exactly that `𝒪_{X,x}` is integrally
closed, i.e. that its delta invariant vanishes.  Tag 0C3U turns a vanishing delta invariant on a
reduced one-dimensional Nagata local ring into a discrete valuation ring, hence a regular local
ring; conversely a regular local ring is integrally closed.  The dimension-zero case is separate:
there the local ring is a reduced zero-dimensional local ring, so a field, which is regular.

## Main results

* `isZero_normalizationQuotientStalk_iff_surjective_stalkMap`: the quotient stalk vanishes
  exactly when the stalk of the module map is an epimorphism.
* `isZero_normalizationQuotientStalk_iff_regular`: the quotient stalk vanishes exactly at a
  regular point.
* `normalizationQuotientStalk_nonzero_iff_mem_singularLocus` is the statement of Tag 0C1R(2)
  about the support of the quotient: precisely the singular points have a nonzero stalk.

## Implementation notes

Exactness of the stalk is `Stacks.SheafOfModules.FlatShortExact.stalkF`, whose preservation of
finite colimits is assembled from the two witnesses
`Stacks.SheafOfModules.FlatShortExact.toSheafColim` and
`Stacks.SheafOfModules.FlatShortExact.forgetStalkColim` through
`Stacks.SheafOfModules.FlatShortExact.compPFC`; feeding those explicitly keeps instance search out
of the composite.  The transfer between the vanishing of the module
stalk, an `AddCommGrpCat` object, and the vanishing of `normalizationQuotientStalk`, a
`ModuleCat` object, is by `Subsingleton` of the common underlying type on both sides.

The one-dimensional hypothesis enters only through Tag 0C3U, and only to exclude dimensions
above one; the dimension bound itself is `ringKrullDim_stalk_le_topologicalKrullDim`.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3U](https://stacks.math.columbia.edu/tag/0C3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.NormalizationStalkAmbient

/-- Surjectivity of the normalization stalk map is surjectivity of the ring map from the local ring
to its integral closure in its fraction ring (Tag 0C3B(2)). -/
private theorem surjective_normalizationStalkMap_iff_surjective_algebraMap_integralClosure
    (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c)) ↔
    Function.Surjective (algebraMap (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) := by
  let _ : IsReduced (X.presheaf.stalk x) := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  let _ : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let e := normalizationStalkAlgEquivIntegralClosureSelf X hX x
  have key : algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) =
      e.toRingEquiv.toRingHom.comp
        (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x)) :=
    RingHom.ext fun a => (e.commutes a).symm
  rw [key]
  exact (EquivLike.comp_surjective _ e.toRingEquiv).symm

/-- An integrally closed local ring of a reduced scheme has surjective normalization stalk map:
by Tag 0C3B(2) the target is the integral closure, and integral closedness says the ring is all
of it. -/
public theorem normalizationStalkMap_surjective_of_isIntegrallyClosed (X : Scheme.{u})
    [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (hclosed : IsIntegrallyClosed (X.presheaf.stalk x)) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c)) := by
  rw [surjective_normalizationStalkMap_iff_surjective_algebraMap_integralClosure]
  intro b
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (K := FractionRing (X.presheaf.stalk x))).mp hclosed b.2
  exact ⟨a, Subtype.ext ha⟩

/-- A surjective normalization stalk map forces the delta invariant of the local ring to vanish:
the image of the ring in its integral closure is everything, so the quotient measuring the
delta invariant is trivial. -/
public theorem deltaInvariant_eq_zero_of_surjective_normalizationStalkMap (X : Scheme.{u})
    [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (hsurj : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c))) :
    Ring.deltaInvariant (X.presheaf.stalk x) = 0 := by
  rw [surjective_normalizationStalkMap_iff_surjective_algebraMap_integralClosure] at hsurj
  rw [Ring.deltaInvariant, LinearMap.range_eq_top.mpr hsurj]
  exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)

/-- The stalk of the normalization quotient vanishes exactly when the stalk of the module map is
an epimorphism, because the stalk functor is exact and therefore commutes with the cokernel. -/
public theorem isZero_normalizationQuotientStalk_iff_surjective_stalkMap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    IsZero (normalizationQuotientStalk X hX x) ↔
      Epi ((Stacks.SheafOfModules.FlatShortExact.stalkF (X := X.toRingedSpace) x).map
        (normalizationModuleMap X hX)) := by
  let φ := normalizationModuleMap X hX
  let T := Stacks.SheafOfModules.FlatShortExact.stalkF (X := X.toRingedSpace) x
  have hpres : PreservesFiniteColimits T := by
    dsimp [T, Stacks.SheafOfModules.FlatShortExact.stalkF]
    exact Stacks.SheafOfModules.FlatShortExact.compPFC
      (SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (Stacks.SheafOfModules.FlatShortExact.toSheafColim X.toRingedSpace)
      (Stacks.SheafOfModules.FlatShortExact.forgetStalkColim x)
  let _ : PreservesFiniteColimits T := hpres
  let _ : PreservesColimit (parallelPair φ 0) T :=
    (hpres.preservesFiniteColimits WalkingParallelPair).preservesColimit
  have hzero : IsZero (T.obj (cokernel φ)) ↔ Epi (T.map φ) :=
    ⟨fun hz => Abelian.epi_of_cokernel_π_eq_zero _
        ((IsZero.of_iso hz (PreservesCokernel.iso T φ).symm).eq_of_tgt _ _),
      fun _ => IsZero.of_iso (isZero_cokernel_of_epi (T.map φ)) (PreservesCokernel.iso T φ)⟩
  have htgt : IsZero (T.obj (cokernel φ)) ↔ IsZero (normalizationQuotientStalk X hX x) :=
    ⟨fun hz => ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp hz),
      fun hz => AddCommGrpCat.isZero_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)⟩
  exact htgt.symm.trans hzero

/-- The stalk of the normalization quotient of a reduced one-dimensional Nagata scheme vanishes
exactly at the regular points. -/
public theorem isZero_normalizationQuotientStalk_iff_regular (X : Scheme.{u}) [IsReduced X]
    (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) (x : X) :
    IsZero (normalizationQuotientStalk X
        (Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
          X hX) x) ↔ x ∈ regularLocus X := by
  let hfin :=
    Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme X hX
  let A := X.presheaf.stalk x
  let _ : IsReduced A := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  let hA : IsNagataRing A := stalk_isNagataRing X hX x
  let _ : IsNoetherianRing A := hA.1
  have hdimLE : ringKrullDim A ≤ 1 := by
    have hle := ringKrullDim_stalk_le_topologicalKrullDim X x
    rw [hdim] at hle
    exact_mod_cast hle
  have hdim_cases : ringKrullDim A = 0 ∨ ringKrullDim A = 1 := by
    cases hdimA : ringKrullDim A using WithBot.recBotCoe with
    | bot =>
        have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
        rw [hdimA] at hnonneg
        exact absurd hnonneg (not_le_of_gt (show (⊥ : WithBot ℕ∞) < 0 by simp))
    | coe d =>
        have hdle : d ≤ (1 : ℕ∞) := by
          apply WithBot.coe_le_coe.mp
          simpa [hdimA] using hdimLE
        rcases Order.le_one_iff.mp hdle with hd0 | hd1
        · exact Or.inl (by simpa [hdimA] using hd0)
        · exact Or.inr (by simpa [hdimA] using hd1)
  have hregular_iff : x ∈ regularLocus X ↔ IsRegularLocalRing A := Iff.rfl
  constructor
  · intro hz
    have hs : Function.Surjective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hfin).c)) :=
      (normalizationModuleStalkMap_epi_iff_ringStalkMap_surjective X hfin x).mp
        ((isZero_normalizationQuotientStalk_iff_surjective_stalkMap X hfin x).mp hz)
    have hδ := deltaInvariant_eq_zero_of_surjective_normalizationStalkMap X hfin x hs
    rcases hdim_cases with hdim0 | hdim1
    · let _ : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by simp [hdim0])
      have hfield : IsField A := Ring.KrullDimLE.isField_of_isReduced
      let _ : Field A := hfield.toField
      exact hregular_iff.mpr inferInstance
    · obtain ⟨hdom, hDVR⟩ :=
        (Ring.deltaInvariant_eq_zero_iff_isDiscreteValuationRing hA hdim1).mp hδ
      let _ : IsDomain A := hdom
      let _ : IsDiscreteValuationRing A := hDVR
      exact hregular_iff.mpr inferInstance
  · intro hxreg
    let _ : IsRegularLocalRing A := hxreg
    have hclosed : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
    have hs := normalizationStalkMap_surjective_of_isIntegrallyClosed X hfin x hclosed
    exact (isZero_normalizationQuotientStalk_iff_surjective_stalkMap X hfin x).mpr
      ((normalizationModuleStalkMap_epi_iff_ringStalkMap_surjective X hfin x).mpr hs)

/-- **Stacks Project, Tag 0C1R(2).** The stalk of the normalization quotient of a reduced
one-dimensional Nagata scheme is nonzero exactly at the singular points. -/
-- The 0C1R "quotient_sheaf" tag is attached, once, in
-- `NormalizationQuotientDirectSum.Basic`, on
-- `normalizationQuotientIsoCoproductSkyscraper` -- the covering declaration for that label.
-- It is not repeated here: one label, one tag, and the attribute refuses a duplicate.
public theorem normalizationQuotientStalk_nonzero_iff_mem_singularLocus (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) (x : X) :
    ¬ IsZero (normalizationQuotientStalk X
        (Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
          X hX) x) ↔ x ∈ singularLocus X :=
  not_congr (isZero_normalizationQuotientStalk_iff_regular X hX hdim x)

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
