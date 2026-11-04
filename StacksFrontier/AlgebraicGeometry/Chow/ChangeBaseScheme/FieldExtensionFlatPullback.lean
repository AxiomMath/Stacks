module

public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper

/-!
# Base change along a finite field extension is a flat pullback over the old base

Let `E/k` be a finite extension of fields, let `X` be a scheme locally of finite type over `k`, and
write `g = Spec E ⟶ Spec k` for the morphism of bases, `π = pullback.fst f g : X_E ⟶ X` for the
projection and `q = pullback.snd f g : X_E ⟶ Spec E` for the new structure morphism.

The group `Z_i(X_E)` admits two descriptions: as cycles for the Chow situation
`Stacks.Chow.fieldChowSituation E` with structure morphism `q`, the target of
`Stacks.Chow.baseChangeCyclePullback`; and as cycles for `Stacks.Chow.fieldChowSituation k` with
structure morphism `π ≫ f`, the target of `Stacks.Chow.flatPullback` along `π`. The two pullbacks
of a cycle have the same coefficient function, so base change along a finite field extension is a
flat pullback over the old base.

## Main results

* `Stacks.Chow.isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension` — the projection `π` is finite
  locally free of rank `[E : k]`, being a base change of `g`.
* `Stacks.Chow.relativeDimension_comp_fieldExtension` — the two relative-dimension functions on a
  scheme over `Spec E` agree: the one taken over `Spec k` through `g`, and the one taken over
  `Spec E` directly.
* `Stacks.Chow.val_baseChangeCyclePullback_eq_val_flatPullback` — the base change of a cycle along
  `E/k` and its flat pullback along `π` over `Spec k` have equal coefficient functions.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0FH8](https://stacks.math.columbia.edu/tag/0FH8)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The projection of a finite field-extension base change -/

/-- The morphism of bases attached to a finite field extension is finite locally free of rank the
degree of the extension. -/
private theorem isFiniteLocallyFreeOfRank_fieldExtension (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (fieldExtensionBaseChangeSituation k E).g
      (Module.finrank k E) :=
  Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field

/-- The morphism of bases attached to a finite field extension is locally of finite type. -/
private theorem locallyOfFiniteType_fieldExtension (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] :
    LocallyOfFiniteType (fieldExtensionBaseChangeSituation k E).g :=
  have := isFiniteLocallyFreeOfRank_fieldExtension k E
  Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)

/-- **Stacks 02KA for a finite field extension.** For `E/k` a finite extension of fields and `X` a
scheme over `k`, the projection `X ×_{Spec k} Spec E ⟶ X` is finite locally free of rank
`[E : k]`. -/
theorem isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g)
      (Module.finrank k E) :=
  have _ := isFiniteLocallyFreeOfRank_fieldExtension k E
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g).flip

/-! ### The two relative-dimension functions -/

/-- The relative dimension of a morphism is the dimension function of the base at the image point
plus the transcendence degree of the residue-field extension. -/
private theorem relativeDimension_eq_add_residueTrdeg {X S : Scheme.{u}}
    (δ : TopologicalSpace.DimensionFunction S) (h : X ⟶ S) (x : X) :
    relativeDimension δ h x = δ (h.base x) + (Cardinal.toNat (residueTrdeg h x) : ℤ) :=
  rfl

/-- The relative dimension over `Spec k` of the morphism of bases `Spec E ⟶ Spec k` attached to a
finite field extension vanishes. -/
private theorem relativeDimension_fieldExtension_eq_zero (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] (y : (fieldChowSituation E).S) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (fieldExtensionBaseChangeSituation k E).g y = 0 := by
  have := isFiniteLocallyFreeOfRank_fieldExtension k E
  have := locallyOfFiniteType_fieldExtension k E
  have hzero : AlgebraicGeometry.RelativeDimension (fieldExtensionBaseChangeSituation k E).g 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)
  have htr := toNat_residueTrdeg_le_of_relativeDimension
    (fieldExtensionBaseChangeSituation k E).g 0 hzero y
  rw [relativeDimension_eq_add_residueTrdeg, fieldChowSituation_dimensionFunction]
  omega

/-- **The two relative-dimension functions on a scheme over a finite extension field agree.** For
`E/k` finite and `W` locally of finite type over `E`, the relative dimension of `W` over `Spec k`
computed through `Spec E ⟶ Spec k` coincides with its relative dimension over `Spec E`. -/
theorem relativeDimension_comp_fieldExtension (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] {W : Scheme.{u}}
    (h : W ⟶ (fieldChowSituation E).S) [LocallyOfFiniteType h] (w : W) :
    relativeDimension (fieldChowSituation k).dimensionFunction
        (h ≫ (fieldExtensionBaseChangeSituation k E).g) w =
      relativeDimension (fieldChowSituation E).dimensionFunction h w := by
  have := locallyOfFiniteType_fieldExtension k E
  rw [relativeDimension_comp_eq_add_trdeg (fieldChowSituation k).dimensionFunction
      (fieldExtensionBaseChangeSituation k E).g h w,
    relativeDimension_eq_add_residueTrdeg (fieldChowSituation E).dimensionFunction h w,
    relativeDimension_fieldExtension_eq_zero, fieldChowSituation_dimensionFunction]

/-! ### Congruence of the flat pullback multiplicity in the Chow situation -/

/-- The coefficient function of the cycle of a closed subscheme depends on the Chow situation and
the structure morphism only through the relative dimension of the point: two situations assigning
the same relative dimension to `x` give the same coefficient there. -/
private theorem closedSubschemeCycleCoeff_congr {C D : ChowSituation.{u}} {X Z : Scheme.{u}}
    (sC : X ⟶ C.S) [LocallyOfFiniteType sC] (sD : X ⟶ D.S) [LocallyOfFiniteType sD]
    (cl : Z ⟶ X) [IsClosedImmersion cl] (k : ℤ) {x : X}
    (hx : relativeDimension C.dimensionFunction sC x =
      relativeDimension D.dimensionFunction sD x) :
    closedSubschemeCycleCoeff C sC cl k x = closedSubschemeCycleCoeff D sD cl k x := by
  rw [closedSubschemeCycleCoeff, closedSubschemeCycleCoeff, hx]

/-- The flat pullback multiplicity depends on the Chow situation and the structure morphism of the
source only through the relative dimension of the point. -/
private theorem flatPullbackWeight_congr {C D : ChowSituation.{u}} {X' X : Scheme.{u}}
    (sC : X' ⟶ C.S) [LocallyOfFiniteType sC] (sD : X' ⟶ D.S) [LocallyOfFiniteType sD]
    (q : X' ⟶ X) (k : ℤ) {x : X'}
    (hx : relativeDimension C.dimensionFunction sC x =
      relativeDimension D.dimensionFunction sD x) :
    flatPullbackWeight C sC q k x = flatPullbackWeight D sD q k x :=
  closedSubschemeCycleCoeff_congr sC sD _ k hx

/-! ### Base change along a finite field extension as a flat pullback -/

/-- **Base change along a finite field extension is a flat pullback over the old base.** For `E/k`
a finite extension of fields, `X` locally of finite type over `k` and
`π = pullback.fst f g : X_E ⟶ X` the projection, the base change
`Stacks.Chow.baseChangeCyclePullback` of a cycle `z ∈ Z_i(X)` — a cycle for the Chow situation of
`E` with structure morphism `pullback.snd f g` — and the flat pullback `Stacks.Chow.flatPullback`
of `z` along `π` — a cycle for the Chow situation of `k` with structure morphism `π ≫ f` — have the
same coefficient function. -/
theorem val_baseChangeCyclePullback_eq_val_flatPullback (k E : Type u) [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g)]
    [Flat (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g)]
    (hπ0 : AlgebraicGeometry.RelativeDimension
      (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g) 0)
    (i : ℤ) (z : CycleGroup (fieldChowSituation k) f i) :
    (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k E) f i z).1 =
      (flatPullback (fieldChowSituation k)
        (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
        (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0
        hπ0 i z).1 := by
  ext x
  have hdim : relativeDimension (fieldChowSituation E).dimensionFunction
        (CategoryTheory.Limits.pullback.snd f (fieldExtensionBaseChangeSituation k E).g) x =
      relativeDimension (fieldChowSituation k).dimensionFunction
        (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) x := by
    rw [CategoryTheory.Limits.pullback.condition]
    exact (relativeDimension_comp_fieldExtension k E
      (CategoryTheory.Limits.pullback.snd f (fieldExtensionBaseChangeSituation k E).g) x).symm
  have hweight := flatPullbackWeight_congr
    (CategoryTheory.Limits.pullback.snd f (fieldExtensionBaseChangeSituation k E).g)
    (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f)
    (CategoryTheory.Limits.pullback.fst f (fieldExtensionBaseChangeSituation k E).g) (i + 0) hdim
  rw [baseChangeCyclePullback_apply, flatPullback_apply, Nat.cast_zero,
    fieldExtensionBaseChangeSituation_c, hweight]

end Stacks.Chow

end
