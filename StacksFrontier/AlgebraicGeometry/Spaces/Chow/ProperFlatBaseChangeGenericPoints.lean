module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# The degree count of Stacks 0EPD at the generic points

In Situation 0EDT let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of good algebraic spaces over `B`, with `f` proper and `g` flat of
relative dimension `r`. For an integral closed subspace `Z ⊆ X` with `f`-image closure `Z'`, and
an integral closed subspace `T' ⊆ Y'`, this file proves the degree count

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`

from a comparison datum at the generic points, which reads the four numbers of the identity as
invariants of a local ring `A` and of a finite free `A`-algebra `B`. In those terms the identity
is

`rank_A(B) · length_A(A) = ∑_𝔮 [κ(𝔮) : κ(A)] · length_{B_𝔮}(B_𝔮)`,

both sides being `length_A(B)`, by freeness on the left and by Stacks 02M0 on the right.

## Main definitions

* `AlgebraicGeometry.Space.GenericPointComparisonDatum`: the local ring `A` of `g^{-1}(Z')` at the
  generic point of `T'` and the semilocal ring `B` of `(g')^{-1}(Z)` along the fibre over that
  point, together with the identification of the four numbers of the degree count with their
  invariants.

## Main results

* `Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule`: for a finite free
  algebra `B` over a local ring `A`,
  `rank_A(B) · length_A(A) = ∑_𝔮 [κ(𝔮) : κ(A)] · length_{B_𝔮}(B_𝔮)`.
* `AlgebraicGeometry.Space.properCycleDegree_mul_flatPullbackMult_eq_finsum`: the degree count at
  one pair `Z`, `T'`, from a comparison datum at that pair.
* `AlgebraicGeometry.Space.properFlatBaseChangeComparison_of_genericPointData`: an inhabitant of
  `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`, from a comparison datum at every
  pair.
* `AlgebraicGeometry.Space.flatPullback_properPushforward_of_genericPointData`: the identity
  `g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')`, from a comparison datum at every pair.
* `AlgebraicGeometry.Space.flatPullback_properPushforward'`: the third assertion of Stacks 0EPD,
  the identity `g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')` for an arbitrary `k`-cycle `α`.

## Implementation notes

A comparison datum asks `B` to be free over `A`, the form `Module.length_of_free_of_finite`
takes. Its two rings live in an arbitrary universe `v`, independent of the universe `u` of the
site.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Length

/-- Let `A` be a commutative local ring and let `B` be an `A`-algebra which is finite and free
as an `A`-module, semilocal and local at each of its maximal ideals, and Artinian over itself.
Then

`rank_A(B) · length_A(A) = ∑_𝔮 [κ(𝔮) : κ(A)] · length_{B_𝔮}(B_𝔮)`,

the sum being over the maximal ideals of `B`. -/
@[ega "IV 21.10.11" "partial"]
theorem finrank_mul_length_eq_sum_finrank_mul_length_localizedModule
    (A : Type u) [CommRing A] [IsLocalRing A] (B : Type v) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] [IsArtinian B B] [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (hfin : ∀ q : MaximalSpectrum B, Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl B) ≠ ⊤) :
    (Module.finrank A B : ℕ∞) * Module.length A A =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl B) := by
  rw [← Module.length_of_free_of_finite A B]
  exact length_eq_sum_finrank_mul_length_localizedModule B hfin

end Stacks.Length

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section GenericPoints

variable (D : BaseSpaceDimensionSituation.{u})
    {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hf'base : f' ≫ sY' = sX') (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sY = sY') (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hg'flat : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')

/-- Comparison data at the generic points for the degree count of Stacks 0EPD. Fix an integral
closed subspace `Z ⊆ X`, write `Z'` for the closure of its image under `f`, and fix an integral
closed subspace `T' ⊆ Y'`. A datum consists of

* `base`, the local ring of the closed subspace `g^{-1}(Z')` at the generic point of `T'`, and
* `fibre`, the semilocal ring of the closed subspace `(g')^{-1}(Z)` along the fibre over that
  generic point, finite and free over `base`,

together with the dictionary between the four numbers of the degree count and invariants of
those two rings: `degree_eq` reads the degree `deg(Z/Z')` of Stacks 0EP1 as the rank of `fibre`
over `base`, `mult_eq` reads the multiplicity `m_{T'}(g^{-1}(Z'))` of Stacks 0EP8 as the length
of `base`, and `componentMult_eq` and `componentDegree_eq` read the multiplicity
`m_T((g')^{-1}(Z))` and the degree `deg(T/T')` at the subspace `component 𝔮` attached to a
maximal ideal `𝔮` of `fibre` as the length of the localization and as the residue degree
`[κ(𝔮) : κ(base)]`. -/
structure GenericPointComparisonDatum
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y') where
  /-- The local ring of `g^{-1}(Z')` at the generic point of `T'`. -/
  base : Type v
  [commRingBase : CommRing base]
  [isLocalRingBase : IsLocalRing base]
  /-- The ring of `(g')^{-1}(Z)` along the fibre over the generic point of `T'`. -/
  fibre : Type v
  [commRingFibre : CommRing fibre]
  [algebraFibre : Algebra base fibre]
  [finiteFibre : Module.Finite base fibre]
  [freeFibre : Module.Free base fibre]
  [artinianFibre : IsArtinian fibre fibre]
  [fintypeMaximalSpectrum : Fintype (MaximalSpectrum fibre)]
  [isLocalHomLocalization : ∀ q : MaximalSpectrum fibre,
    IsLocalHom (algebraMap base (Localization.AtPrime q.asIdeal))]
  /-- The integral closed subspace of `X'` at the maximal ideal `q` of `fibre`. -/
  component : MaximalSpectrum fibre → IntegralClosedSubspace D.site D.base D.base_mem X'
  /-- Distinct maximal ideals name distinct subspaces. -/
  injective_component : Function.Injective component
  /-- The multiplicity `m_{T'}(g^{-1}(Z'))`, as a natural number. -/
  mult : ℕ
  /-- That number is the length of `base`. -/
  length_base : Module.length base base = mult
  /-- The multiplicity `m_{component q}((g')^{-1}(Z))`, as a natural number. -/
  componentMult : MaximalSpectrum fibre → ℕ
  /-- That number is the length of the localization of `fibre` at `q`. -/
  length_localization : ∀ q : MaximalSpectrum fibre,
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl fibre) = componentMult q
  /-- The degree `deg(Z/Z')` of Stacks 0EP1 is the rank of `fibre` over `base`. -/
  degree_eq : properCycleDegree D sX hX sY hY f Z = (Module.finrank base fibre : ℤ)
  /-- The multiplicity `m_{T'}(g^{-1}(Z'))` of Stacks 0EP8 is `mult`. -/
  mult_eq : flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z) T' = (mult : ℤ)
  /-- The multiplicity of `component q` in `(g')^{-1}(Z)` is `componentMult q`. -/
  componentMult_eq : ∀ q : MaximalSpectrum fibre,
    flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z (component q) =
      (componentMult q : ℤ)
  /-- The degree of `component q` over `T'` is the residue degree at `q`. -/
  componentDegree_eq : ∀ q : MaximalSpectrum fibre,
    properCycleMult D sX' hX' sY' hY' f' (component q) T' =
      (Module.finrank (IsLocalRing.ResidueField base)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ)
  /-- An integral closed subspace of `X'` which is not one of the `component q` contributes
  nothing to the right-hand side of the degree count. -/
  vanishing : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X',
    (∀ q : MaximalSpectrum fibre, component q ≠ T) →
      flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
        properCycleMult D sX' hX' sY' hY' f' T T' = 0

/-- The degree count of Stacks 0EPD at one pair of generic points. For an integral closed
subspace `Z ⊆ X` with `f`-image closure `Z'`, and an integral closed subspace `T' ⊆ Y'`, given an
`AlgebraicGeometry.Space.GenericPointComparisonDatum` at that pair,

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`,

the sum on the right being over all integral closed subspaces of `X'`. -/
theorem properCycleDegree_mul_flatPullbackMult_eq_finsum
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y')
    (data : GenericPointComparisonDatum.{u, v} D sX' hX' sX hX sY' hY' sY hY (f := f) (f' := f')
      hg'base hgbase r hgflat hgr hg'flat hg'r Z T') :
    properCycleDegree D sX hX sY hY f Z *
        flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z) T' =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T' := by
  classical
  obtain ⟨A, B, comp, hcomp, m, hlenA, cm, hlenB, hdeg, hmult, hcm, hcd, hvan⟩ := data
  have hsub : (Function.support fun T : IntegralClosedSubspace D.site D.base D.base_mem X' =>
      flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
        properCycleMult D sX' hX' sY' hY' f' T T') ⊆
      ((Finset.univ.image comp :
        Finset (IntegralClosedSubspace D.site D.base D.base_mem X')) : Set _) := by
    intro T hT
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hc
    exact hT (hvan T fun q hq => hc ⟨q, hq⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsub,
    Finset.sum_image fun x _ y _ hxy => hcomp hxy, hdeg, hmult,
    Finset.sum_congr rfl fun q _ => by rw [hcm q, hcd q]]
  have hring := Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule A B
    fun q => by rw [hlenB q]; exact ENat.natCast_ne_top _
  simp only [hlenA, hlenB] at hring
  have hnat : Module.finrank A B * m =
      ∑ q : MaximalSpectrum B, Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) * cm q := by
    exact_mod_cast hring
  exact_mod_cast hnat.trans (Finset.sum_congr rfl fun q _ => mul_comm _ _)

/-- A comparison datum at every pair of an integral closed subspace of `X` and an integral
closed subspace of `Y'` gives an inhabitant of
`AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`. -/
theorem properFlatBaseChangeComparison_of_genericPointData
    (hdata : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
        (T' : IntegralClosedSubspace D.site D.base D.base_mem Y'),
      Nonempty (GenericPointComparisonDatum.{u, v} D sX' hX' sX hX sY' hY' sY hY (f := f)
        (f' := f') hg'base hgbase r hgflat hgr hg'flat hg'r Z T')) :
    ProperFlatBaseChangeComparison D sX' hX' sX hX sY' hY' sY hY (f := f) (f' := f')
      hg'base hgbase r hgflat hgr hg'flat hg'r :=
  ⟨fun Z T' => (hdata Z T').elim fun data =>
    properCycleDegree_mul_flatPullbackMult_eq_finsum D sX' hX' sX hX sY' hY' sY hY hg'base
      hgbase r hgflat hgr hg'flat hg'r Z T' data⟩

include hf'base hfbase in
/-- In Situation 0EDT let the four corners of a cartesian square of good algebraic spaces over
`B` be good, let `f : X ⟶ Y` be proper and let `g : Y' ⟶ Y` be flat of relative dimension `r`.
Then for every `k`-cycle `α` on `X`

`g^*f_*α = f'_*(g')^*α`

in `Z_{k+r}(Y')`, provided there is an `AlgebraicGeometry.Space.GenericPointComparisonDatum` at
every pair of an integral closed subspace of `X` and an integral closed subspace of `Y'`. -/
theorem flatPullback_properPushforward_of_genericPointData (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (hdata : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
        (T' : IntegralClosedSubspace D.site D.base D.base_mem Y'),
      Nonempty (GenericPointComparisonDatum.{u, v} D sX' hX' sX hX sY' hY' sY hY (f := f)
        (f' := f') hg'base hgbase r hgflat hgr hg'flat hg'r Z T'))
    (k n : ℤ) (hkn : k + (r : ℤ) = n) (α : CycleGroup D sX k) :
    flatPullbackMap D sY' hY' sY hY g hgbase r hgflat hgr k n hkn
        (properCyclePushforward D sX hX sY hY hfbase hfproper.2.1.2 k α) =
      properCyclePushforward D sX' hX' sY' hY' hf'base
        (isProper_of_isPullback D.site D.base D.base_mem hX'.1 hX.1 hY'.1 hY.1 sq hfproper).2.1.2
        n (flatPullbackMap D sX' hX' sX hX g' hg'base r hg'flat hg'r k n hkn α) :=
  flatPullback_properPushforward D sX' hX' sX hX sY' hY' sY hY hg'base hf'base hfbase hgbase r
    hgflat hgr hg'flat hg'r sq hfproper
    (properFlatBaseChangeComparison_of_genericPointData D sX' hX' sX hX sY' hY' sY hY hg'base
      hgbase r hgflat hgr hg'flat hg'r hdata) k n hkn α

/-- The identity `g^*f_*α = f'_*(g')^*α` in `Z_{k+r}(Y')`, for a cartesian square of good
algebraic spaces over `B` with `f` proper and `g` flat of relative dimension `r`, and for an
arbitrary `k`-cycle `α` on `X`. -/
@[stacks 0EPD "third assertion: the identity g^* f_* α = f'_* (g')^* α in Z_{k+r}(Y') for an
  arbitrary k-cycle α, with no comparison datum and no numerical identity carried"]
alias flatPullback_properPushforward' := flatPullback_properPushforward_of_isPullback

end GenericPoints

end AlgebraicGeometry.Space

end
