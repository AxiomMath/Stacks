module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalLayerVanishing
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeIsoStructureSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.PuncturedSpectrumSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalBottomStage

/-!
# The first half of the proof of [Stacks, Tag 0F2D]

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor. Write `U` for the punctured
spectrum of `A` and `U₀` for the closed subscheme of `U` cut out by `f𝒪_U`, which is the punctured
closed fibre. The tower of infinitesimal neighbourhoods `U₀ ⊆ U₁ ⊆ U₂ ⊆ ⋯` of `U₀` in `U` is a
tower of first-order thickenings whose layers are all `𝒪_{U₀}`, so the source's exact sequence
`Pic(U_{n+1}) → Pic(U_n) → H²(U₀, 𝒪_{U₀})` of [Stacks, Tag 0C6R] lifts every class once
`H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`.

This file assembles that: the identification of `U₀` with the punctured closed fibre, the
generation of `f𝒪_U` on charts, and the vanishing, and feeds them to
`Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_infinitesimalTower_of_principal`.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.puncturedPrincipalIdeal`: the ideal sheaf `f𝒪_U`.
* `Stacks.PuncturedSpectrumPicard.puncturedPrincipalImmersion`: the closed immersion `U₀ ⟶ U` it
  cuts out.
* `Stacks.PuncturedSpectrumPicard.puncturedPrincipalSubschemeIso`: that `U₀` is the punctured
  closed fibre.

## Main results

* `Stacks.PuncturedSpectrumPicard.ideal_ker_liftCoborder_puncturedPrincipal`: `f𝒪_U` is generated
  on every affine chart by the restriction of `f`.
* `Stacks.PuncturedSpectrumPicard.eq_zero_sheafH_bottomStructureSheaf`: the vanishing of `H³` of
  local cohomology of `A/fA` at the closed point gives `H²(U₀, 𝒪_{U₀}) = 0`.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_puncturedSpectrum`: **the first
  half of the proof of [Stacks, Tag 0F2D]**, under hypotheses (2) and (4) of the tag alone.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace Stacks.PuncturedSpectrumPicard

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  TopCat.Sheaf
  structureSheafRing
  SheafOfModules.toSheaf

/-- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives. This repeats the local
instance of `StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower`. -/
local instance hasExtAbelianSheafFirstHalf (Y : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  hasExt_of_enoughInjectives _

open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdeal baseIdealSheaf_ideal)
open Stacks.Thickenings (nthOrderInfinitesimalNeighbourhood nthOrderZeroIso globalRestrict)
open Stacks.LocalCohomology
  (eq_zero_sheafH_unit_puncturedClosedFibre_of_isZero_localCohomologyWithSupportIn)

variable (A : Type u) [CommRing A] [IsLocalRing A] (f : A)

/-- The ideal sheaf `f𝒪_U` on the punctured spectrum of `A`. -/
abbrev puncturedPrincipalIdeal :
    (Stacks.Divisors.puncturedSpectrum A).toScheme.IdealSheafData :=
  baseIdealSheaf A (Ideal.span {f}) (Stacks.Divisors.puncturedSpectrum A).ι

/-- The closed immersion `U₀ ⟶ U` of the subscheme of the punctured spectrum cut out by
`f𝒪_U`. -/
abbrev puncturedPrincipalImmersion :
    (puncturedPrincipalIdeal A f).subscheme ⟶
      (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  (puncturedPrincipalIdeal A f).subschemeι

/-- **The subscheme of the punctured spectrum cut out by `f𝒪_U` is the punctured closed
fibre.** It is the fibre product `U ×_{Spec A} Spec(A/fA)` by
`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback`, and that fibre product is the
preimage of `U` under `Spec(A/fA) ⟶ Spec A`. -/
def puncturedPrincipalSubschemeIso :
    (puncturedPrincipalIdeal A f).subscheme ≅
      (Stacks.Algebraization.puncturedClosedFibre A f).toScheme :=
  baseIdealSubschemeIsoPullback A (Ideal.span {f})
      (Stacks.Divisors.puncturedSpectrum A).ι ≪≫
    pullbackSymmetry _ _ ≪≫
    pullbackRestrictIsoRestrict (Stacks.Algebraization.closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)

/-! ### The ideal sheaf is generated on charts by `f` -/

/-- The image of `f` in the global functions on the canonical open neighbourhood of the image of
`U₀ ⟶ U`. -/
abbrev puncturedPrincipalScalar :
    Γ((puncturedPrincipalImmersion A f).coborderRange.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    ((puncturedPrincipalImmersion A f).coborderRange.ι ≫
      (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom f

/-- The defining ideal sheaf of the closed-immersion factorization of `U₀ ⟶ U` is `f𝒪` on the
canonical open neighbourhood of the image. -/
theorem ker_liftCoborder_puncturedPrincipal :
    (puncturedPrincipalImmersion A f).liftCoborder.ker =
      baseIdealSheaf A (Ideal.span {f})
        ((puncturedPrincipalImmersion A f).coborderRange.ι ≫
          (Stacks.Divisors.puncturedSpectrum A).ι) := by
  rw [Stacks.Algebraization.ker_liftCoborder_eq_comap,
    Scheme.IdealSheafData.ker_subschemeι, baseIdealSheaf_comap]

/-- **`f𝒪_U` is generated on every affine chart by the restriction of `f`.** This is the
hypothesis `hK` of `Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom`. -/
theorem ideal_ker_liftCoborder_puncturedPrincipal
    (V : (puncturedPrincipalImmersion A f).coborderRange.toScheme.affineOpens) :
    (puncturedPrincipalImmersion A f).liftCoborder.ker.ideal V =
      Ideal.span {globalRestrict
        (puncturedPrincipalImmersion A f).coborderRange.toScheme
        (puncturedPrincipalScalar A f) V.1} := by
  rw [ker_liftCoborder_puncturedPrincipal, baseIdealSheaf_ideal, baseIdeal, Ideal.map_span,
    Set.image_singleton, Ideal.map_span, Set.image_singleton]

/-! ### The vanishing on the bottom stage -/

/-- **Hypothesis (4) of [Stacks, Tag 0F2D] gives `H²(U₀, 𝒪_{U₀}) = 0`.** The vanishing of `H³` of
local cohomology of `A/fA` at the closed point is the vanishing of `H²` of the structure sheaf of
the punctured closed fibre, and the bottom stage of the tower of infinitesimal neighbourhoods is
the punctured closed fibre. -/
theorem eq_zero_sheafH_bottomStructureSheaf [IsNoetherianRing A] (hf : f ∈ maximalIdeal A)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (y : CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf
        (nthOrderInfinitesimalNeighbourhood
          (puncturedPrincipalImmersion A f) 0).ringCatSheaf).obj
          (bottomStructureSheaf (puncturedPrincipalImmersion A f))) 2) :
    y = 0 :=
  Stacks.Cohomology.SchemeIso.eq_zero_sheafH_of_iso
    ((puncturedPrincipalSubschemeIso A f).symm ≪≫
      nthOrderZeroIso (puncturedPrincipalImmersion A f)) 2
    (fun x =>
      eq_zero_sheafH_unit_puncturedClosedFibre_of_isZero_localCohomologyWithSupportIn
        f hf 2 (by norm_num)
        (by rw [show ((2 : ℕ) : ℤ) + 1 = 3 from by norm_num]; exact hvanish3) x) y

/-! ### `f` is a nonzerodivisor on the charts -/

/-- A regular element of a commutative ring is a nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_isSMulRegular {R : Type*} [CommRing R] {a : R}
    (h : IsSMulRegular R a) : a ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_iff.mpr
    ⟨fun z hz => h (by simpa using hz), fun z hz => h (by simpa [mul_comm] using hz)⟩

/-- **The image of `f` is a nonzerodivisor on every affine chart.** The charts of the canonical
open neighbourhood of the image of `U₀ ⟶ U` are opens of `Spec A`, and multiplication by a
nonzerodivisor of `A` is injective on the sections of the structure sheaf over any open, because
a localization is flat. This is the hypothesis `hf` of
`Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom`. -/
theorem mem_nonZeroDivisors_puncturedPrincipalScalar (hreg : IsSMulRegular A f)
    (V : (puncturedPrincipalImmersion A f).coborderRange.toScheme.affineOpens) :
    globalRestrict (puncturedPrincipalImmersion A f).coborderRange.toScheme
        (puncturedPrincipalScalar A f) V.1 ∈
      nonZeroDivisors
        Γ((puncturedPrincipalImmersion A f).coborderRange.toScheme, V.1) :=
  mem_nonZeroDivisors_of_isSMulRegular
    (Stacks.Algebraization.isSMulRegular_structureSheafSections A hreg
      ((Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ
        ((puncturedPrincipalImmersion A f).coborderRange.ι ''ᵁ V.1)))

/-! ### The first half of the tag -/

/-- **The first half of the proof of [Stacks, Tag 0F2D].** Let `(A, 𝔪)` be a Noetherian local
ring and let `f ∈ 𝔪` be a nonzerodivisor with `H³_𝔪(A/fA) = 0`. Then every Picard class on the
bottom stage of the tower of infinitesimal neighbourhoods of `U₀` in the punctured spectrum `U`
extends to a family of classes along the whole tower, each the pullback of the next.

Only hypotheses (2) and (4) of the tag are used. The tower is
`Stacks.PuncturedSpectrumPicard.infinitesimalTower` of
`Stacks.PuncturedSpectrumPicard.puncturedPrincipalImmersion`, the layers are all `𝒪_{U₀}` because
`f` is a nonzerodivisor generating the ideal sheaf on every chart, and the single-stage lift is
the exact sequence of [Stacks, Tag 0C6R]. -/
@[stacks 0F2D "the first half of the source's proof at the punctured spectrum itself, under the \
source's own hypotheses (2) f a nonzerodivisor and (4) H³_𝔪(A/fA) = 0 and nothing else: every \
Picard class on U₀ extends to a family along the tower of infinitesimal neighbourhoods of U₀ in \
U, each the pullback of the next. The per-stage vanishing H²(U_n's ideal sheaf) = 0 is proved \
here, not assumed: the layers are identified with 𝒪_{U₀} by multiplication by f^{n+1} \
(Stacks.Thickenings.idealSheafIsoStructureSheafNthOrderBottom, which is where (2) enters) and \
H²(U₀,𝒪_{U₀}) = 0 is derived from (4). NOT covered: the tag's own conclusion, surjectivity of \
colim_{U₀ ⊆ U' ⊆ U} Pic(U') → Pic(U₀), which is the second half and needs Stacks 0EKZ, hence \
Stacks 0EIR part (2); hypotheses (1) f-adic completeness and (3) finiteness of H¹_𝔪(A/fA), \
H²_𝔪(A/fA) are inputs of that half alone and do not appear here"]
theorem exists_isCompatiblePullback_puncturedSpectrum [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular A f)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (c₀ : Stacks.Picard.ofScheme
      (nthOrderInfinitesimalNeighbourhood (puncturedPrincipalImmersion A f) 0)) :
    ∃ c : (n : ℕ) → Stacks.Picard.ofScheme
        ((infinitesimalTower (puncturedPrincipalImmersion A f)).obj n),
      c 0 = c₀ ∧
        IsCompatiblePullback (infinitesimalTower (puncturedPrincipalImmersion A f)) c :=
  exists_isCompatiblePullback_infinitesimalTower_of_principal
    (puncturedPrincipalImmersion A f) (puncturedPrincipalScalar A f)
    (ideal_ker_liftCoborder_puncturedPrincipal A f)
    (mem_nonZeroDivisors_puncturedPrincipalScalar A f hreg)
    (eq_zero_sheafH_bottomStructureSheaf A f hf hvanish3) c₀

/-- **Every invertible module on the punctured closed fibre extends along the tower of
infinitesimal neighbourhoods**, for a nonzerodivisor `f ∈ 𝔪` of a Noetherian local ring with
`H³_𝔪(A/fA) = 0`. This is
`Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_puncturedSpectrum` with the class
read on the punctured closed fibre, which is the bottom stage of the tower by
`Stacks.PuncturedSpectrumPicard.puncturedPrincipalSubschemeIso` and
`Stacks.Thickenings.nthOrderZeroIso`. -/
theorem exists_isCompatiblePullback_puncturedClosedFibre [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular A f)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (c₀ : Stacks.Picard.ofScheme
      (Stacks.Algebraization.puncturedClosedFibre A f).toScheme) :
    ∃ c : (n : ℕ) → Stacks.Picard.ofScheme
        ((infinitesimalTower (puncturedPrincipalImmersion A f)).obj n),
      c 0 = Stacks.Picard.schemePullbackClass
          (((puncturedPrincipalSubschemeIso A f).symm ≪≫
            nthOrderZeroIso (puncturedPrincipalImmersion A f)).inv) c₀ ∧
        IsCompatiblePullback (infinitesimalTower (puncturedPrincipalImmersion A f)) c :=
  exists_isCompatiblePullback_puncturedSpectrum A f hf hreg hvanish3 _

end Stacks.PuncturedSpectrumPicard

end
