module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ChartStalkAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ContractionStalk
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.FirstArrowStalk
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.TwistStalkModule
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.BiproductStalk
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.LinearAlgebra.UnitalRowKernelMap
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the Euler sequence on projective space

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = P^n_R` for
`Proj R[T]` with structure morphism `f : X ⟶ Spec R`. The Euler sequence

`0 ⟶ Ω_{X/R} ⟶ 𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X ⟶ 0`

is short exact.

Exactness is checked on stalks. Fix a point `x` and a coordinate `Tᵢ` outside its homogeneous
prime, so `x` lies on the standard chart `D₊(Tᵢ)`. Multiplication by `Tᵢ` identifies the stalk of
`𝒪_X(-1)` at `x` with the local ring `B = 𝒪_{X,x}`, hence the stalk of the middle term with
`B^{n+1}`; under that identification the second arrow becomes contraction with the row
`(T₀/Tᵢ, …, Tₙ/Tᵢ)`, whose `i`-th entry is `1`, and the first arrow carries the differential
`d(Tⱼ/Tᵢ)` to `eⱼ - (Tⱼ/Tᵢ) eᵢ`. Those vectors are a basis of the kernel of the row, and the
`d(Tⱼ/Tᵢ)` generate the stalk of `Ω_{X/R}`, so the first arrow is injective with image exactly
that kernel.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerSequence`: the Euler sequence,
  with its two arrows named, is short exact.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.exists_shortExact_eulerSequence`: the form in
  which the source states it, namely that such a short exact sequence exists.
* `twistingSheafZeroStalkEquiv_stalkMap_eulerContraction`: at a point lying on the chart
  `D₊(Tᵢ)`, the stalk of the second arrow is contraction with the row `(T₀/Tᵢ, …, Tₙ/Tᵢ)`, whose
  `i`-th entry is `1`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.germ_chartFracSection` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.relativeDifferentialsStalkLinearEquiv_chartDiffGerm`:
  the germ of the affine coordinate `Tⱼ/Tᵢ` is its image in the local ring, and the universal
  derivation carries its differential to the Kähler differential of that image.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.span_range_chartDiffGerm_eq_top`: the differentials
  of the affine coordinates generate the stalk of `Ω_{X/R}`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkCoord_stalkMap_eulerFirstArrow`: the
  first arrow carries the germ of `d(Tⱼ/Tᵢ)` to `eⱼ - (Tⱼ/Tᵢ) eᵢ`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.injective_stalkMap_eulerFirstArrow` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.exists_stalkMap_eulerFirstArrow_eq`: on the stalk
  at a point of `D₊(Tᵢ)` the first arrow is injective with image the kernel of the second.

## Implementation notes

Three different scalar actions on the stalks are in play and they are not interchangeable. The
stalk functor on sheaves of modules is linear over the `RingCat`-valued stalk of the structure
sheaf; the identification of the stalk of a twisting sheaf with the local ring is linear over the
repo's transported action; and the Kähler differentials of the stalk are linear over the
`CommRingCat`-valued stalk. They are reconciled by
`AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'` and by
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk_ringCat_smul`; the
latter is a theorem and not a definitional identity, which is why the linearity of
`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkMap` is proved by hand rather than obtained
by composing bundled maps.

This has four consequences for the proofs below.

`rw` cannot move a scalar between two of these actions: the two sides are definitionally equal
but their instance paths differ, so keyed matching fails and the rewrite reports that it did not
find the pattern. Every such step is an `Eq.trans`/`congrArg` chain in term mode, where the defeq
is discharged by unification instead.

`rw [map_sum]` on a sum indexed by the summands of the biproduct exhausts the `isDefEq` budget.
The sum is therefore pushed through the maps by `map_sum _ _ Finset.univ` supplied as a term.

`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkCoord` is a plain definition, so `rw` does
not see through it; `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkCoord_def` exists for
that purpose and is needed before any rewrite that must reach the trivialization underneath.

`Stacks.AlgebraicGeometry.ProjEulerSequence.stalkRingEquiv` is deliberately not `private`: a
private constant may not appear in the signature of a public declaration, and it appears in the
statement of the linearity of the coordinates.

A point of `Proj R[T]` is spelled here as a point of `ProjectiveSpectrum.top (polyGrading R n)`,
whereas the identification of the stalk of the relative differentials is stated for a point of a
scheme. Reaching one spelling from the other unfolds `AlgebraicGeometry.Proj`, which instance
search does not do, so five things have to be arranged by hand.

`Stacks.RelativeDifferentialStalk.moduleStalkRelativeDifferentials` is not found at all, and is
re-registered locally at both spellings of the stalk, `↥(SheafOfModules.stalkObj …)` and
`ToType (TopCat.Presheaf.stalk …)`. Neither registration covers the other, because
`AlgebraicGeometry.SheafOfModules.stalkObj` is a plain definition.

The second registration must spell the sheaf `Scheme.Hom.relativeDifferentials (projToSpecCoeff
R n)` rather than `Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials R n`: the
abbreviation's `.val` carries the ring sheaf as `projRingSheaf`, the identification carries it as
`(AlgebraicGeometry.Proj _).ringCatSheaf`, and the two give different discrimination keys.

`DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))` has no instance and cannot be supplied by
one, so `Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv` and its germ
lemma are applied with the argument given positionally as `Classical.decEq _`.

The local ring must be spelled `Stacks.AlgebraicGeometry.ProjPolyChart.projStalk R n x`; at the
`ProjectiveSpectrum.Proj.structureSheaf` spelling the `Algebra` and `Module` instances are not
found. Where a lemma would infer it from the type of `coordRatio`, it is pinned by passing
`(B := projStalk R n x)`.

A section variable used only inside a proof is not included automatically; `include hx in` does
it, and must be written before the declaration's docstring rather than after.

Exactness and monomorphy are each proved in their own declaration, and exactness is split once
more over the points of the space, because a single declaration doing two of these steps exhausts
its `isDefEq` budget. For the same reason `Mono` is obtained from
`AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap` applied to the morphism written
out, not by rewriting with it: supplying the morphism pins the sheaf of rings, where leaving it
implicit makes the elaborator discover it through `AlgebraicGeometry.Proj`.

The first arrow `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerFirstArrow` is the morphism
chosen from the unique-existence statement `Tag 08RM`, pinned by
`Stacks.AlgebraicGeometry.ProjEulerSequence.universalRelativeDerivation_postcomp_eulerFirstArrow`,
so it is determined. A genuinely constructive body is available in principle: the proof of
`AlgebraicGeometry.SheafOfModules.universalDerivation_isUniversal` exhibits the factorization as
`e.symm D` for a composite of `PresheafOfModules.sheafificationHomEquiv` with
`AlgebraicGeometry.SheafOfModules.presheafDifferentialsEquiv`, and exporting that bijection would
give the arrow as a function application. It would not change the axioms the result depends on,
since sheafification already uses choice.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The ideal underlying the homogeneous prime of a point of `Proj` is prime. -/
local instance isPrime_toIdeal_exactness (x : ProjectiveSpectrum.top (polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The stalk of the sheaf of relative differentials of `P^n_R ⟶ Spec R` at `x` as a module over
the local ring at `x`, in the spelling the stalk functor on sheaves of modules produces. -/
local instance moduleStalkProjDifferentials
    (x : ProjectiveSpectrum.top (polyGrading R n)) :
    Module (projStalk R n x)
      ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
        (projDifferentials R n)) :=
  Stacks.RelativeDifferentialStalk.moduleStalkRelativeDifferentials (projToSpecCoeff R n) x

/-- The same module structure, at the spelling of the stalk of the underlying presheaf of
abelian groups, which is what the identification with the Kähler differentials uses. -/
local instance moduleStalkProjDifferentialsPresheaf
    (x : ProjectiveSpectrum.top (polyGrading R n)) :
    Module (projStalk R n x)
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials (projToSpecCoeff R n)).val.presheaf x)) :=
  Stacks.RelativeDifferentialStalk.moduleStalkRelativeDifferentials (projToSpecCoeff R n) x

section Point

variable (x : ProjectiveSpectrum.top (polyGrading R n)) (i : Fin (n + 1))
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)

/-- The comparison of the `RingCat`-valued stalk of the structure sheaf, over which the stalk
functor is linear, with the `CommRingCat`-valued one, which is the local ring. -/
abbrev stalkRingEquiv :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (projRingSheaf (polyGrading R n)).obj x) ≃+*
      ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x

/-- **The `k`-th coordinate of an element of the stalk of `𝒪_X(-1)^{⊕ (n+1)}`**, read in the
local ring at `x` through multiplication by `Tᵢ`. -/
def eulerStalkCoord (k : Fin (n + 1))
    (d : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))) :
    ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.stalk x) :=
  twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
    ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (biproduct.π (twistMinusOneFamily R n) k)).hom d)

/-- The `k`-th coordinate is the image of the `k`-th component of the germ under the
trivialization of the stalk of `𝒪_X(-1)` by `Tᵢ`. -/
theorem eulerStalkCoord_def (k : Fin (n + 1))
    (d : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))) :
    eulerStalkCoord R n x i hx k d =
      twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (biproduct.π (twistMinusOneFamily R n) k)).hom d) :=
  rfl

/-- The coordinates are additive. -/
theorem eulerStalkCoord_add (k : Fin (n + 1))
    (d d' : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))) :
    eulerStalkCoord R n x i hx k (d + d') =
      eulerStalkCoord R n x i hx k d + eulerStalkCoord R n x i hx k d' :=
  (congrArg (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx)
    (map_add _ d d')).trans (map_add _ _ _)

/-- The coordinates are linear over the local ring: the stalk functor is linear over the
`RingCat`-valued stalk, and the two actions correspond under `stalkRingEquiv`. -/
theorem eulerStalkCoord_smul (k : Fin (n + 1))
    (b : ToType ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.stalk x))
    (d : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))) :
    eulerStalkCoord R n x i hx k
        ((stalkRingEquiv R n x).symm b • d) =
      b * eulerStalkCoord R n x i hx k d := by
  have hπ := (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
    (biproduct.π (twistMinusOneFamily R n) k)).hom.map_smul
      ((stalkRingEquiv R n x).symm b) d
  have hbridge := associatedModuleSheafStalk_ringCat_smul (polyGrading R n)
    (twistGrading (polyGrading R n) (-1)) x ((stalkRingEquiv R n x).symm b)
    ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (biproduct.π (twistMinusOneFamily R n) k)).hom d)
  rw [RingEquiv.apply_symm_apply] at hbridge
  exact (congrArg (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx)
    (hπ.trans hbridge.symm)).trans (map_smul _ b _)

/-- An element of the stalk of `𝒪_X(-1)^{⊕ (n+1)}` is determined by its coordinates: it is the
sum of the images of its components under the inclusions of the summands. -/
theorem eulerStalkCoord_injective
    {d d' : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))}
    (h : ∀ k, eulerStalkCoord R n x i hx k d = eulerStalkCoord R n x i hx k d') :
    d = d' := by
  have hcomp : ∀ k, (AlgebraicGeometry.SheafOfModules.stalkMap
        (projRingSheaf (polyGrading R n)) x
        (biproduct.π (twistMinusOneFamily R n) k)).hom d =
      (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (biproduct.π (twistMinusOneFamily R n) k)).hom d' := fun k =>
    (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx).injective (h k)
  have hd := AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading R n)) x (twistMinusOneFamily R n) d
  have hd' := AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading R n)) x (twistMinusOneFamily R n) d'
  rw [← hd, ← hd']
  exact congrArg _ (funext hcomp)

/-- **The stalk of the second arrow is contraction with the row `(T₀/Tᵢ, …, Tₙ/Tᵢ)`.** -/
theorem twistingSheafZeroStalkEquiv_stalkMap_eulerContraction
    (d : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n))) :
    twistingSheafZeroStalkEquiv (polyGrading R n) x
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerContraction R n)).hom d) =
      Stacks.LinearAlgebra.unitalRow (coordRatio R n x i hx)
        (fun k => eulerStalkCoord R n x i hx k d) := by
  have hd := AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
    (projRingSheaf (polyGrading R n)) x (twistMinusOneFamily R n) d
  have hmorph : ∀ k : Fin (n + 1),
      AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
            (biproduct.ι (twistMinusOneFamily R n) k) ≫
          AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
            (eulerContraction R n) =
        AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (contraction R n k) := fun k =>
    (((AlgebraicGeometry.SheafOfModules.stalkFunctor (projRingSheaf (polyGrading R n)) x).map_comp
        (biproduct.ι (twistMinusOneFamily R n) k) (eulerContraction R n)).symm.trans
      (congrArg (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x)
        (biproduct_ι_comp_eulerContraction R n k)))
  have hterm : ∀ k : Fin (n + 1),
      twistingSheafZeroStalkEquiv (polyGrading R n) x
          ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
              (eulerContraction R n)).hom
            ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
                (biproduct.ι (twistMinusOneFamily R n) k)).hom
              ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
                  (biproduct.π (twistMinusOneFamily R n) k)).hom d))) =
        coordRatio R n x i hx k * eulerStalkCoord R n x i hx k d := fun k =>
    (congrArg (twistingSheafZeroStalkEquiv (polyGrading R n) x)
        (congrArg
          (fun φ : AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
                (twistMinusOneFamily R n k) ⟶
              AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
                (twistingSheaf (polyGrading R n) 0) =>
            φ.hom ((AlgebraicGeometry.SheafOfModules.stalkMap
              (projRingSheaf (polyGrading R n)) x
              (biproduct.π (twistMinusOneFamily R n) k)).hom d))
          (hmorph k))).trans
      (tw0_stalkMap_contraction R n x i hx k _)
  have key : twistingSheafZeroStalkEquiv (polyGrading R n) x
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerContraction R n)).hom d) =
      ∑ k : Fin (n + 1), coordRatio R n x i hx k * eulerStalkCoord R n x i hx k d := by
    refine Eq.trans (congrArg (fun z => twistingSheafZeroStalkEquiv (polyGrading R n) x
      ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (eulerContraction R n)).hom z)) hd.symm) ?_
    refine Eq.trans (congrArg (twistingSheafZeroStalkEquiv (polyGrading R n) x)
      (map_sum (AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading R n)) x (eulerContraction R n)).hom
        (fun k => (AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading R n)) x
            (biproduct.ι (twistMinusOneFamily R n) k)).hom
          ((AlgebraicGeometry.SheafOfModules.stalkMap
              (projRingSheaf (polyGrading R n)) x
              (biproduct.π (twistMinusOneFamily R n) k)).hom d))
        Finset.univ)) ?_
    refine Eq.trans (map_sum (twistingSheafZeroStalkEquiv (polyGrading R n) x) _ Finset.univ) ?_
    exact Finset.sum_congr rfl fun k _ => hterm k
  rw [Stacks.LinearAlgebra.unitalRow_apply]
  exact key

/-- **The germ of `Tⱼ/Tᵢ` is the image of the affine coordinate.** At a point of the standard
chart `D₊(Tᵢ)` the germ of the regular function `Tⱼ/Tᵢ` is the image of the affine coordinate
`Tⱼ/Tᵢ` of the chart ring under the comparison of that ring with the local ring. -/
theorem germ_chartFracSection
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    ((ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).presheaf.germ
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom
        (chartFracSection R n i j.1) =
      chartToStalk R n i x hx (chartCoord R n i j) := by
  refine (Proj.stalkIso' (polyGrading R n) x).injective
    (HomogeneousLocalization.val_injective _ ?_)
  refine Eq.trans (congrArg HomogeneousLocalization.val
    (Proj.stalkIso'_germ (polyGrading R n)
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb
      (chartFracSection R n i j.1))) ?_
  refine Eq.trans (chartFracSection_val R n i j.1 ⟨x, hxb⟩) ?_
  refine Eq.trans ?_ (congrArg HomogeneousLocalization.val
    (stalkIso'_chartToStalk R n i x hx (chartCoord R n i j))).symm
  rw [show HomogeneousLocalization.mapId (polyGrading R n) (Submonoid.powers_le.mpr hx)
        (chartCoord R n i j) =
      HomogeneousLocalization.mk ⟨1 • 1, ⟨MvPolynomial.X j.1, X_mem_smul R n j.1⟩,
        ⟨(MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ^ 1,
          SetLike.pow_mem_graded 1 (X_mem_one R n i)⟩,
        Submonoid.powers_le.mpr hx ⟨1, rfl⟩⟩ from rfl, HomogeneousLocalization.val_mk]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by ring))

/-- **The stalk of the relative differentials carries the germ of `d(Tⱼ/Tᵢ)` to the universal
differential of the affine coordinate `Tⱼ/Tᵢ`**, under the identification of that stalk with the
Kähler differentials of the local ring at `x`. -/
theorem relativeDifferentialsStalkLinearEquiv_chartDiffGerm
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap (projToSpecCoeff R n)).hom x
    @Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv _ _
        (projToSpecCoeff R n) x (Classical.decEq _) (chartDiffGerm R n x i hxb j.1) =
      KaehlerDifferential.D
        (Stacks.RelativeDifferentialStalkMap.inverseImageStalk (projToSpecCoeff R n) x)
        (projStalk R n x)
        (chartToStalk R n i x hx (chartCoord R n i j)) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap (projToSpecCoeff R n)).hom x
  refine Eq.trans
    (@Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv_germ_d _ _
      (projToSpecCoeff R n) x (Classical.decEq _)
      (OrderDual.toDual (⟨ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i),
        hxb⟩ : TopologicalSpace.OpenNhds x))
      (chartFracSection R n i j.1)) ?_
  exact congrArg _ (germ_chartFracSection R n x i hx hxb j)

include hx in
/-- **The germs of `d(Tⱼ/Tᵢ)`, `j ≠ i`, generate the stalk of the sheaf of relative
differentials.** They correspond to the differentials of the affine coordinates of the chart
`D₊(Tᵢ)`, which generate the differentials of the local ring at `x`. -/
theorem span_range_chartDiffGerm_eq_top
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    Submodule.span (projStalk R n x)
        (Set.range fun j : {j : Fin (n + 1) // j ≠ i} => chartDiffGerm R n x i hxb j.1) = ⊤ := by
  let := algebraChartStalk R n i x hx
  let := algebraRStalk R n i x hx
  let := isLocalization_chartToStalk R n i x hx
  let := isScalarTower_R_chart_stalk R n i x hx
  let := algebraRInverseImage R n x
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap (projToSpecCoeff R n)).hom x
  let := isScalarTower_R_inverseImage_stalk R n i x hx
  let g : {j : Fin (n + 1) // j ≠ i} →
      KaehlerDifferential
        (Stacks.RelativeDifferentialStalkMap.inverseImageStalk (projToSpecCoeff R n) x)
        (projStalk R n x) := fun j =>
    KaehlerDifferential.D
      (Stacks.RelativeDifferentialStalkMap.inverseImageStalk (projToSpecCoeff R n) x)
      (projStalk R n x) (chartToStalk R n i x hx (chartCoord R n i j))
  let Θ := @Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv _ _
    (projToSpecCoeff R n) x (Classical.decEq _)
  let L : KaehlerDifferential
        (Stacks.RelativeDifferentialStalkMap.inverseImageStalk (projToSpecCoeff R n) x)
        (projStalk R n x) →ₗ[projStalk R n x]
      ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
        (projDifferentials R n)) := Θ.symm.toLinearMap
  have hspan : Submodule.span (projStalk R n x) (Set.range g) = ⊤ :=
    Stacks.AlgebraicGeometry.ProjPolyChart.span_range_D_chartToStalk_eq_top R n i x hx
  have hL : ∀ j : {j : Fin (n + 1) // j ≠ i}, L (g j) = chartDiffGerm R n x i hxb j.1 :=
    fun j => (LinearEquiv.symm_apply_eq Θ).mpr
      (relativeDifferentialsStalkLinearEquiv_chartDiffGerm R n x i hx hxb j).symm
  calc Submodule.span (projStalk R n x)
          (Set.range fun j : {j : Fin (n + 1) // j ≠ i} => chartDiffGerm R n x i hxb j.1)
      = Submodule.span (projStalk R n x) (Set.range (L ∘ g)) :=
        congrArg _ (congrArg Set.range (funext fun j => (hL j).symm))
    _ = Submodule.map L (Submodule.span (projStalk R n x) (Set.range g)) := by
        rw [Submodule.map_span, Set.range_comp]
    _ = ⊤ := by
        rw [hspan, Submodule.map_top]
        exact LinearMap.range_eq_top.mpr fun p => ⟨Θ p, Θ.symm_apply_apply p⟩

/-- **The first arrow carries the germ of `d(Tⱼ/Tᵢ)` to the kernel generator
`eⱼ - (Tⱼ/Tᵢ) eᵢ`**: its `k`-th coordinate is `δ_{kj} - (Tⱼ/Tᵢ) δ_{ki}`. -/
theorem eulerStalkCoord_stalkMap_eulerFirstArrow
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (j k : Fin (n + 1)) :
    eulerStalkCoord R n x i hx k
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerFirstArrow R n)).hom (chartDiffGerm R n x i hxb j)) =
      Stacks.LinearAlgebra.kernelGen (coordRatio R n x i hx) i j k := by
  classical
  refine (Proj.stalkIso' (polyGrading R n) x).injective
    (HomogeneousLocalization.val_injective _ ?_)
  rw [eulerStalkCoord_def, val_tw_stalkMap_π_eulerFirstArrow R n x i hxb hx j k,
    Stacks.LinearAlgebra.kernelGen_apply, map_sub, map_mul,
    HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul, val_coordRatio]
  rcases eq_or_ne k j with rfl | hkj
  · rcases eq_or_ne k i with rfl | hki
    · simp [HomogeneousLocalization.val_one, mul_comm]
    · simp [hki, HomogeneousLocalization.val_one, HomogeneousLocalization.val_zero, mul_comm]
  · rcases eq_or_ne k i with rfl | hki
    · simp [hkj, HomogeneousLocalization.val_one, HomogeneousLocalization.val_zero, mul_comm]
    · simp [hkj, hki, HomogeneousLocalization.val_zero, mul_comm]

/-- **The stalk of the first arrow, read in coordinates**: the `B`-linear map sending a germ of a
relative differential to the `n+1` coordinates of its image, in the trivialization of `𝒪_X(-1)`
at `x` by the coordinate `Tᵢ`. -/
def eulerStalkMap :
    ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
        (projDifferentials R n)) →ₗ[projStalk R n x] (Fin (n + 1) → projStalk R n x) where
  toFun p k := eulerStalkCoord R n x i hx k
    ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (eulerFirstArrow R n)).hom p)
  map_add' p q := funext fun k =>
    (congrArg (eulerStalkCoord R n x i hx k)
        (map_add (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerFirstArrow R n)).hom p q)).trans
      (eulerStalkCoord_add R n x i hx k _ _)
  map_smul' b p := funext fun k => by
    have hb : b • p = (stalkRingEquiv R n x).symm b • p :=
      (congrArg (fun c : projStalk R n x => c • p)
            ((stalkRingEquiv R n x).apply_symm_apply b).symm).trans
        (AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq'
          (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x
          (projDifferentials R n).val ((stalkRingEquiv R n x).symm b) p)
    exact (congrArg (eulerStalkCoord R n x i hx k)
        ((congrArg (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
            (eulerFirstArrow R n)).hom hb).trans
          (map_smul _ ((stalkRingEquiv R n x).symm b) p))).trans
      (eulerStalkCoord_smul R n x i hx k b _)

/-- The coordinates of the image of the germ of `d(Tⱼ/Tᵢ)` are the kernel generator
`eⱼ - (Tⱼ/Tᵢ) eᵢ`, as a vector. -/
private theorem eulerStalkMap_chartDiffGerm
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    eulerStalkMap R n x i hx (chartDiffGerm R n x i hxb j.1) =
      Stacks.LinearAlgebra.kernelGen (coordRatio R n x i hx) i j.1 :=
  funext fun k => eulerStalkCoord_stalkMap_eulerFirstArrow R n x i hx hxb j.1 k

include hx in
/-- **The stalk of the first arrow at a point of the chart `D₊(Tᵢ)` is injective.** The germs of
`d(Tⱼ/Tᵢ)` generate the stalk and go to the basis `eⱼ - (Tⱼ/Tᵢ) eᵢ` of the kernel of the
coordinate row, so no nonzero combination of them is killed. -/
theorem injective_stalkMap_eulerFirstArrow
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    Function.Injective
      ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (eulerFirstArrow R n)).hom) := by
  classical
  have hinj := Stacks.LinearAlgebra.injective_of_span_eq_top (B := projStalk R n x)
    (coordRatio_self R n x i hx) (eulerStalkMap R n x i hx)
    (fun j : {j : Fin (n + 1) // j ≠ i} => chartDiffGerm R n x i hxb j.1)
    (eulerStalkMap_chartDiffGerm R n x i hx hxb)
    (span_range_chartDiffGerm_eq_top R n x i hx hxb)
  exact fun p q hpq =>
    hinj (funext fun k => congrArg (eulerStalkCoord R n x i hx k) hpq)

include hx in
/-- **A germ of `𝒪_X(-1)^{⊕ (n+1)}` killed by the second arrow comes from the first.** Its
coordinate vector is annihilated by the row `(T₀/Tᵢ, …, Tₙ/Tᵢ)`, hence is a combination of the
vectors `eⱼ - (Tⱼ/Tᵢ) eᵢ`, which are the images of the germs of `d(Tⱼ/Tᵢ)`. -/
theorem exists_stalkMap_eulerFirstArrow_eq
    (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (m : ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (twistMinusOneSum R n)))
    (hm : (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (eulerSurjection R n)).hom m = 0) :
    ∃ p, (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (eulerFirstArrow R n)).hom p = m := by
  classical
  have hcomp : AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (eulerSurjection R n) =
      AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerContraction R n) ≫
        AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (twistingSheafZeroIsoUnit (polyGrading R n)).hom :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (projRingSheaf (polyGrading R n)) x).map_comp
      (eulerContraction R n) (twistingSheafZeroIsoUnit (polyGrading R n)).hom
  have hcancel : ∀ y, (AlgebraicGeometry.SheafOfModules.stalkMap
          (projRingSheaf (polyGrading R n)) x
          (twistingSheafZeroIsoUnit (polyGrading R n)).inv).hom
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (twistingSheafZeroIsoUnit (polyGrading R n)).hom).hom y) = y := by
    have h := ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (projRingSheaf (polyGrading R n)) x).map_comp
        (twistingSheafZeroIsoUnit (polyGrading R n)).hom
        (twistingSheafZeroIsoUnit (polyGrading R n)).inv).symm.trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading R n)) x).map
        (twistingSheafZeroIsoUnit (polyGrading R n)).hom_inv_id).trans
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading R n)) x).map_id _))
    exact fun y => congrArg (fun φ => ModuleCat.Hom.hom φ y) h
  rw [hcomp] at hm
  have hzero : (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
      (eulerContraction R n)).hom m = 0 :=
    (hcancel ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
        (eulerContraction R n)).hom m)).symm.trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (twistingSheafZeroIsoUnit (polyGrading R n)).inv).hom hm).trans (map_zero _))
  have hrow : Stacks.LinearAlgebra.unitalRow (coordRatio R n x i hx)
      (fun k => eulerStalkCoord R n x i hx k m) = 0 :=
    (twistingSheafZeroStalkEquiv_stalkMap_eulerContraction R n x i hx m).symm.trans
      ((congrArg (twistingSheafZeroStalkEquiv (polyGrading R n) x) hzero).trans (map_zero _))
  obtain ⟨p, hp⟩ := Stacks.LinearAlgebra.exists_apply_eq_of_unitalRow_eq_zero
    (B := projStalk R n x) (coordRatio_self R n x i hx) (eulerStalkMap R n x i hx)
    (fun j : {j : Fin (n + 1) // j ≠ i} => chartDiffGerm R n x i hxb j.1)
    (eulerStalkMap_chartDiffGerm R n x i hx hxb) hrow
  exact ⟨p, eulerStalkCoord_injective R n x i hx fun k => congrFun hp k⟩

end Point

/-- **The Euler sequence is exact on the stalk at a point.** At a point lying on the chart
`D₊(Tᵢ)` the second arrow is contraction with the unital row `(T₀/Tᵢ, …, Tₙ/Tᵢ)`, and the germs
of `d(Tⱼ/Tᵢ)` are carried onto generators of the kernel of that row. -/
theorem exact_stalk_eulerSequence (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ((CategoryTheory.ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
          (eulerFirstArrow_comp_eulerSurjection R n)).map
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading R n)) x)).Exact := by
  classical
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro m hm
  obtain ⟨i, hx⟩ := exists_X_notMem_asHomogeneousIdeal R n x
  exact exists_stalkMap_eulerFirstArrow_eq R n x i hx
    (mem_basicOpen_X_of_notMem R n x i hx) m hm

/-- **The Euler sequence is exact in the middle**, exactness of a short complex of sheaves of
modules being a stalkwise condition. -/
theorem exact_eulerSequence :
    (CategoryTheory.ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
      (eulerFirstArrow_comp_eulerSurjection R n)).Exact :=
  (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (CategoryTheory.ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
      (eulerFirstArrow_comp_eulerSurjection R n))).mpr (exact_stalk_eulerSequence R n)

/-- **The first arrow of the Euler sequence is a monomorphism.** Monomorphy is checked on stalks,
where the germs of `d(Tⱼ/Tᵢ)` generate and go to a basis of the kernel of the coordinate row. -/
theorem mono_eulerFirstArrow : CategoryTheory.Mono (eulerFirstArrow R n) :=
  (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap (eulerFirstArrow R n)).mpr
    fun x => by
      classical
      obtain ⟨i, hx⟩ := exists_X_notMem_asHomogeneousIdeal R n x
      exact injective_stalkMap_eulerFirstArrow R n x i hx (mem_basicOpen_X_of_notMem R n x i hx)

/-- **The Euler sequence of projective space is short exact**: the first arrow is a monomorphism,
the second an epimorphism, and the sequence is exact in the middle. -/
@[sga "7 XVII 5.1" "more general"]
theorem shortExact_eulerSequence :
    (CategoryTheory.ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
      (eulerFirstArrow_comp_eulerSurjection R n)).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.mk' (exact_eulerSequence R n) (mono_eulerFirstArrow R n)
    (epi_eulerSurjection R n)

/-- **There is a short exact sequence `0 ⟶ Ω ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0`** on projective
`n`-space over a commutative ring, with `Ω` the sheaf of differentials relative to the base. -/
@[stacks 0FMH, sga "6 VIII 5.2" "special case", sga "7 XVII 5.1" "more general"]
theorem exists_shortExact_eulerSequence :
    ∃ (a : projDifferentials R n ⟶ twistMinusOneSum R n)
      (b : twistMinusOneSum R n ⟶ SheafOfModules.unit (projRingSheaf (polyGrading R n)))
      (h : a ≫ b = 0), (CategoryTheory.ShortComplex.mk a b h).ShortExact :=
  ⟨eulerFirstArrow R n, eulerSurjection R n, eulerFirstArrow_comp_eulerSurjection R n,
    shortExact_eulerSequence R n⟩

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
