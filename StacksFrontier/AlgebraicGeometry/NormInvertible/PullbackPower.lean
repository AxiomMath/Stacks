module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.PicardData
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The norm of a pullback is the tensor power

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` of degree `d` on functions
(`Stacks.Norm.MorphismNorm`, Tag 0BD1) and let `𝒩` be an invertible `𝒪_Y`-module. This file
proves

  `Norm_f(f^*𝒩) ≅ 𝒩^{⊗ d}`,

the **second clause** of [Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY), and
hence that the homomorphism of Picard groups of `Stacks.Divisors.normPicardData` satisfies
`Stacks.Divisors.HasNormPullbackPower`. With the first clause
(`Stacks.Divisors.exists_normPicardAddMonoidHom`) that completes Tag 0BCY.

## The argument

Tag 0BCY's own proof computes with transition functions, and so does this one, through
`Stacks.SheafOfModules.isoOfChartGenerators`: two modules carrying a generator over each member
of one open covering family, with the same pairwise transition units, are isomorphic.

The covering family is a family of opens of `Y` on which `𝒩` is trivial, which exists because
`𝒩` is invertible (`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`, the converse
half of Tag 0B8M). Over such an open both sides acquire a generator from the generator `t` of
`𝒩` there:

* `Stacks.Divisors.normPullbackGen`, the norm of the pullback of `t`;
* `Stacks.Divisors.tensorPowerGen`, the `d`-fold tensor power of `t`.

Their transition units agree, and this is the whole content: if `t_j = a · t_i` on an overlap,
then the pullbacks satisfy `f^*t_j = f^♯(a) · f^*t_i`
(`Stacks.SheafOfModules.generatorRatioUnit_pullbackGenerator`), the norm sends that to
`N(f^♯(a)) = a^d` (`Stacks.Divisors.normUnitsMap_pullback`, which is where the *defining*
property of a norm of degree `d` on pulled-back functions enters), and the `d`-th tensor power
has transition unit `a^d` as well
(`Stacks.SheafOfModules.generatorRatioUnit_tensorPowerGenerator`). So both families have
transition units `a^d` and the two modules are isomorphic.

Note that no cohomology appears. The source's proof identifies `Pic` with `H¹(X, 𝒪_X^*)`
(Tag 09NU); that route is not taken here and is not needed.

## Main definitions

* `Stacks.Divisors.normPullbackChart` and `Stacks.Divisors.normPullbackChartGen`: the covering
  family of trivializing opens of `𝒩` and its generators.
* `Stacks.Divisors.normPullbackGen` and `Stacks.Divisors.tensorPowerGen`: the chart generators of
  the two modules being compared.

## Main results

* `Stacks.Divisors.generatorRatioUnit_normPullbackGen`: the two chart generator families have the
  same transition units.
* `Stacks.Divisors.normInvertiblePullbackIso`: **the norm of the pullback is the `d`-fold tensor
  power.**
* `Stacks.Divisors.hasNormPullbackPower_normPicardData`: **Tag 0BCY's pullback--power clause**,
  for the homomorphism of `Stacks.Divisors.normPicardData`.
* `Stacks.Divisors.exists_normPicardData_hasNormPullbackPower`: Tag 0BCY in full — a norm of
  invertible modules together with a homomorphism `Pic(X) → Pic(Y)` induced by it and satisfying
  the pullback--power formula.

## Implementation notes

**Which invertibility class.** The repository carries two Tag 01CS predicates with the same body.
`Stacks.SheafOfModules.IsInvertible` is the one the Picard group and
`Stacks.Divisors.HasNormPullbackPower` key on; `tensorPowerModule'` keys on
`AlgebraicGeometry.SheafOfModules.IsInvertible`. They are related in both directions by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, which is crossed here and
nowhere restated. No further bridge lemma identifying the two classes is added here.

`Stacks.SheafOfModules.Invertible.tensorPowerModule' L (d : ℤ)` is a `noncomputable abbrev` for
`Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf _ L (d : ℤ)`, which is the constant
`HasNormPullbackPower` names, so the comparison proved below is accepted there with no
restatement. The two instance arguments are propositions and therefore definitionally equal.

The chart generators are indexed by the points of `Y`, which is a `Type u`, as
`isoOfChartGenerators` requires.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-! ### The trivializing cover of the target and its generators -/

section Charts

variable (L : Y.Modules)
  (hL : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property L)

/-- A trivializing open of `L` around each point of `Y`, from the converse half of Tag 0B8M. -/
noncomputable def normPullbackChart (y : Y.carrier) : Y.Opens :=
  (exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y).choose

/-- The point lies in its own chart. -/
theorem mem_normPullbackChart (y : Y.carrier) : y ∈ normPullbackChart L hL y :=
  (exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y).choose_spec.choose

/-- The charts cover `Y`. -/
theorem normPullbackChart_cover :
    (⊤ : Y.Opens) ≤ ⨆ y : Y.carrier, normPullbackChart L hL y := fun y _ =>
  Opens.mem_iSup.2 ⟨y, mem_normPullbackChart L hL y⟩

/-- The generator of `L` on its chart. -/
noncomputable def normPullbackChartGen (y : Y.carrier) :
    GeneratorSections Y.toRingedSpace L (normPullbackChart L hL y) :=
  ⟨(exists_bijective_smul_of_isInvertible
      (X := Y.toRingedSpace) L y).choose_spec.choose_spec.choose,
    (exists_bijective_smul_of_isInvertible
      (X := Y.toRingedSpace) L y).choose_spec.choose_spec.choose_spec⟩

end Charts

/-! ### The two chart generator families -/

section Comparison

variable (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) (L : Y.Modules)
  (hL : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property L)

include hL

/-- The pullback of `L`, which is invertible. -/
alias isInvertible_pullbackObj := isInvertible_modulePullback_of_isInvertible

variable [IsFinite f]

/-- The pullback of `L` has a trivializing target cover, so its norm is defined. -/
theorem hasTrivializingTargetCover_pullbackObj :
    HasTrivializingTargetCover f ((modulePullback f.toLRSHom.toShHom).obj L) :=
  hasTrivializingTargetCover_of_isFinite_of_isInvertible f _
    (isInvertible_pullbackObj f L hL)

/-- **The chart generator of the norm of the pullback**: the norm of the pullback of the chart
generator of `L`. -/
noncomputable def normPullbackGen (y : Y.carrier) {A : Y.Opens}
    (h : A ≤ normPullbackChart L hL y) :
    GeneratorSections Y.toRingedSpace
      (normInvertible f N.toMorphismNormMap ((modulePullback f.toLRSHom.toShHom).obj L)) A :=
  normGenerator f N.toMorphismNormMap ((modulePullback f.toLRSHom.toShHom).obj L)
    (hasTrivializingTargetCover_pullbackObj f L hL) A
    (pullbackGenerator f L hL A
      (generatorRestrict L h (normPullbackChartGen L hL y)))

/-! ### Restriction of the chart generator families -/

/-- The restriction of `normPullbackGen` along `B ≤ A` is `normPullbackGen` on `B`. -/
theorem generatorRestrict_normPullbackGen (y : Y.carrier) {A B : Y.Opens}
    (h : A ≤ normPullbackChart L hL y) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        (normInvertible f N.toMorphismNormMap
          ((modulePullback f.toLRSHom.toShHom).obj L)) k
        (normPullbackGen f N L hL y h) =
      normPullbackGen f N L hL y (k.trans h) := by
  refine (generatorRestrict_normGenerator f N ((modulePullback f.toLRSHom.toShHom).obj L)
    (hasTrivializingTargetCover_pullbackObj f L hL) k
    (pullbackGenerator f L hL A
      (generatorRestrict L h (normPullbackChartGen L hL y)))).trans ?_
  refine congrArg (normGenerator f N.toMorphismNormMap
    ((modulePullback f.toLRSHom.toShHom).obj L)
    (hasTrivializingTargetCover_pullbackObj f L hL) B) ?_
  refine (pullbackGenerator_restrict f L hL k
    (generatorRestrict L h (normPullbackChartGen L hL y))).trans ?_
  exact congrArg (pullbackGenerator f L hL B)
    (generatorRestrict_trans L h k (normPullbackChartGen L hL y))

variable [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
  (structureSheafRing Y.toRingedSpace).property L]

/-- **The chart generator of the `d`-fold tensor power**: the `d`-fold tensor power of the chart
generator of `L`. -/
noncomputable def tensorPowerGen (y : Y.carrier) {A : Y.Opens}
    (h : A ≤ normPullbackChart L hL y) :
    GeneratorSections Y.toRingedSpace
      (Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ)) A :=
  tensorPowerGenerator L (generatorRestrict L h (normPullbackChartGen L hL y)) d

/-- The restriction of `tensorPowerGen` along `B ≤ A` is `tensorPowerGen` on `B`. -/
theorem generatorRestrict_tensorPowerGen (y : Y.carrier) {A B : Y.Opens}
    (h : A ≤ normPullbackChart L hL y) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        (Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ)) k
        (tensorPowerGen L hL y h) =
      tensorPowerGen L hL y (k.trans h) :=
  (tensorPowerGenerator_restrict L k
      (generatorRestrict L h (normPullbackChartGen L hL y)) d).trans
    (congrArg (fun g => tensorPowerGenerator L g d)
      (generatorRestrict_trans L h k (normPullbackChartGen L hL y)))

/-! ### The transition units agree -/

/-- **The two chart generator families have the same transition units.** On an overlap the chart
generators of `L` differ by a unit `a`; the pullbacks then differ by `f^♯(a)`, whose norm is
`a ^ d`, and the `d`-fold tensor power differs by `a ^ d` as well. -/
theorem generatorRatioUnit_normPullbackGen (y z : Y.carrier) (A : Y.Opens)
    (hy : A ≤ normPullbackChart L hL y) (hz : A ≤ normPullbackChart L hL z) :
    generatorRatioUnit (X := Y.toRingedSpace)
        (Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ)) A
        (tensorPowerGen L hL z hz) (tensorPowerGen L hL y hy) =
      generatorRatioUnit (X := Y.toRingedSpace)
        (normInvertible f N.toMorphismNormMap
          ((modulePullback f.toLRSHom.toShHom).obj L)) A
        (normPullbackGen f N L hL z hz) (normPullbackGen f N L hL y hy) := by
  unfold tensorPowerGen normPullbackGen
  refine (generatorRatioUnit_tensorPowerGenerator L A _ _ d).trans ?_
  refine Eq.symm ((generatorRatioUnit_normGenerator f N.toMorphismNormMap _ _ A _ _).trans ?_)
  exact (congrArg (normUnitsMap f N.toMorphismNormMap A)
    (generatorRatioUnit_pullbackGenerator f L hL A _ _)).trans (normUnitsMap_pullback f N A _)

/-! ### The comparison -/

/-- **The norm of the pullback of an invertible module is its `d`-fold tensor power.** -/
noncomputable def normInvertiblePullbackIso :
    normInvertible f N.toMorphismNormMap ((modulePullback f.toLRSHom.toShHom).obj L) ≅
      Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ) :=
  isoOfChartGenerators (X := Y.toRingedSpace)
    (normInvertible f N.toMorphismNormMap ((modulePullback f.toLRSHom.toShHom).obj L))
    (Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ))
    (fun y => normPullbackGen f N L hL y le_rfl)
    (fun y => tensorPowerGen L hL y le_rfl)
    (fun i j A hi hj =>
      ((congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace)
            (Invertible.tensorPowerModule' (X := Y.toRingedSpace) L (d : ℤ)) A)
          (generatorRestrict_tensorPowerGen L hL j le_rfl hj)
          (generatorRestrict_tensorPowerGen L hL i le_rfl hi)).trans
        (generatorRatioUnit_normPullbackGen f N L hL i j A hi hj)).trans
      (congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace)
            (normInvertible f N.toMorphismNormMap
              ((modulePullback f.toLRSHom.toShHom).obj L)) A)
          (generatorRestrict_normPullbackGen f N L hL j le_rfl hj)
          (generatorRestrict_normPullbackGen f N L hL i le_rfl hi)).symm)
    (normPullbackChart_cover L hL)


end Comparison

/-! ### Tag 0BCY's pullback--power clause -/

/-- **Stacks Project, Tag 0BCY**, the pullback--power clause: the homomorphism of Picard groups
induced by a norm of degree `d` carries the class of `f^*𝒩` to the class of `𝒩^{⊗ d}`, for every
invertible `𝒪_Y`-module `𝒩`.

Together with `Stacks.Divisors.exists_normPicardAddMonoidHom`, which is the tag's other clause,
this completes Tag 0BCY. -/
@[stacks 0BCY "the pullback-power formula"]
theorem hasNormPullbackPower_normPicardData (g : X ⟶ Y) [IsFinite g] (e : ℕ)
    (M : MorphismNorm g e) :
    HasNormPullbackPower g e (normPicardData g e M).picardMap := by
  intro P hP
  have := hP
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property P :=
    (isInvertible_iff_algebraicGeometry _ _ P).mp hP
  refine Eq.trans (normPicardData_picardMap_picardClass g M
    ((modulePullback g.toLRSHom.toShHom).obj P) (isInvertible_pullbackObj g P hP)) ?_
  exact (picardClass_eq_iff Y.presheaf (structureSheaf Y.sheaf).property _ _ _ _).mpr
    ⟨normInvertiblePullbackIso g M P hP⟩

/-- **Stacks Project, Tag 0BCY in full**: a finite morphism carrying a norm of degree `d` on
functions induces a norm of invertible modules, a homomorphism of abelian groups
`Pic(X) → Pic(Y)` computing it on classes, and that homomorphism satisfies
`Norm_f(f^*𝒩) ≅ 𝒩^{⊗ d}`.

No `@[stacks]` attribute is placed here: both of the tag's clauses already carry it, the first on
`Stacks.Divisors.exists_normPicardAddMonoidHom` and the second on
`Stacks.Divisors.hasNormPullbackPower_normPicardData`, and bundling them is not a third clause. -/
theorem exists_normPicardData_hasNormPullbackPower (g : X ⟶ Y) [IsFinite g] (e : ℕ)
    (M : MorphismNorm g e) :
    ∃ D : NormPicardData g e M, HasNormPullbackPower g e D.picardMap :=
  ⟨normPicardData g e M, hasNormPullbackPower_normPicardData g e M⟩

end Stacks.Divisors

end
