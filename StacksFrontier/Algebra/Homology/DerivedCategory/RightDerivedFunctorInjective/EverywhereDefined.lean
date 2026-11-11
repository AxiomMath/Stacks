module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.AcyclicResolutions
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwise
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness

/-!
# Higher right derived functors of an everywhere defined `RF`

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories. The right derived functor
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is *everywhere defined* when the right derived functor of
`K⁺(F) ⋙ Q⁺_ℬ : K⁺(𝒜) ⥤ D⁺(ℬ)` relative to the quasi-isomorphisms of `K⁺(𝒜)` is defined at every
object of `K⁺(𝒜)` in the sense of [Stacks, Tag 05S9]: the ind-object `(s : X ⟶ X') ↦ F(X')`
is essentially constant (`CategoryTheory.Functor.IsRightDerivable`, [Stacks, Tag 05SV]). Under
this assumption alone, this file defines `RF` and the higher right derived functors
`R ⁱ F = H ⁱ ∘ RF : 𝒜 ⥤ ℬ` of [Stacks, Tag 015A]. When `𝒜` has enough injectives, `RF` is
everywhere defined, and these functors are the functors `CategoryTheory.Functor.rightDerivedPlus`
built from injective resolutions.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusOfIsRightDerivable`: the functor
  `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` of an everywhere defined right derived functor.
* `CategoryTheory.Functor.rightDerivedOfIsRightDerivable`: `R ⁱ F = H ⁱ ∘ RF`, [Stacks, Tag 015A].

## Main results

* `CategoryTheory.Functor.isRightDerivable_mapHomotopyCategoryPlus_comp_Qh`: if `𝒜` has enough
  injectives, then `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined.
* `CategoryTheory.Functor.rightDerivedOfIsRightDerivable_eq_rightDerivedPlus`: with enough
  injectives, `R ⁱ F` is the functor `CategoryTheory.Functor.rightDerivedPlus` of the
  injective-resolution construction.

## Implementation notes

The value of `RF` is Mathlib's total right derived functor
`CategoryTheory.Functor.totalRightDerived` of `K⁺(F) ⋙ Q⁺_ℬ` along `Q⁺_𝒜`. Its existence is
deduced from everywhere-definedness by
`CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`, which uses that the
quasi-isomorphisms of `K⁺(𝒜)` admit a left calculus of fractions.

## References

* [Stacks, Tag 015A], the higher right derived functors
* [Stacks, Tag 05SV], an everywhere defined right derived functor
* [Stacks, Tag 06XN], everywhere-definedness from a class of objects computing `RF`
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory C] in
/-- If `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined, i.e. the right derived functor of
`K⁺(F) ⋙ Q⁺_ℬ` relative to the quasi-isomorphisms of `K⁺(𝒜)` is defined at every object, then
`K⁺(F) ⋙ Q⁺_ℬ` has a pointwise right derived functor along `Q⁺_𝒜`. -/
theorem hasPointwiseRightDerivedFunctor_of_isRightDerivable_mapHomotopyCategoryPlus
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
  have := (quasiIsoPlus_isSaturated (C := C)).hasLeftCalculusOfFractions
  hasPointwiseRightDerivedFunctor_of_isRightDerivable _ _ h

/-- The right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` of an additive functor `F : 𝒜 ⥤ ℬ` between
abelian categories, under the assumption that it is everywhere defined: the right derived functor
of `K⁺(F) ⋙ Q⁺_ℬ` along the localization `Q⁺_𝒜 : K⁺(𝒜) ⥤ D⁺(𝒜)` at the quasi-isomorphisms. -/
noncomputable def rightDerivedFunctorPlusOfIsRightDerivable
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable_mapHomotopyCategoryPlus h
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)

/-- The canonical natural transformation `K⁺(F) ⋙ Q⁺_ℬ ⟶ Q⁺_𝒜 ⋙ RF` exhibiting
`CategoryTheory.Functor.rightDerivedFunctorPlusOfIsRightDerivable` as a right derived functor. -/
noncomputable def rightDerivedFunctorPlusOfIsRightDerivableUnit
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlusOfIsRightDerivable h :=
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable_mapHomotopyCategoryPlus h
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)

instance (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    (F.rightDerivedFunctorPlusOfIsRightDerivable h).IsRightDerivedFunctor
      (F.rightDerivedFunctorPlusOfIsRightDerivableUnit h) (HomotopyCategory.Plus.quasiIso C) := by
  have := F.hasPointwiseRightDerivedFunctor_of_isRightDerivable_mapHomotopyCategoryPlus h
  dsimp only [rightDerivedFunctorPlusOfIsRightDerivable,
    rightDerivedFunctorPlusOfIsRightDerivableUnit]
  infer_instance

/-- **Stacks 015A.** The `i`-th right derived functor `R ⁱ F = H ⁱ ∘ RF : 𝒜 ⥤ ℬ` of an additive
functor `F : 𝒜 ⥤ ℬ` between abelian categories, assuming that `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere
defined (`h`). Here `RF` is `CategoryTheory.Functor.rightDerivedFunctorPlusOfIsRightDerivable`,
an object `A` of `𝒜` is sent to the complex `A[0]` concentrated in degree `0`, and `H ⁱ` is the
`i`-th cohomology functor `D⁺(ℬ) ⥤ ℬ`. -/
@[stacks 015A]
noncomputable def rightDerivedOfIsRightDerivable
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (i : ℤ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlusOfIsRightDerivable h ⋙
    DerivedCategory.Plus.homologyFunctor D i

end

section EnoughInjectives

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- If `𝒜` has enough injectives, a quasi-isomorphism between bounded below complexes of
injective objects is an isomorphism in `K⁺(𝒜)`. -/
private lemma isIso_of_quasiIso_of_injective {X Y : HomotopyCategory.Plus C} (s : X ⟶ Y)
    (hs : HomotopyCategory.Plus.quasiIso C s) [∀ n : ℤ, Injective (X.obj.as.X n)]
    [∀ n : ℤ, Injective (Y.obj.as.X n)] : IsIso s := by
  have : (𝟭 (HomotopyCategory.Plus C)).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
    HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso _
  have : (𝟭 (HomotopyCategory.Plus C)).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
    hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  let α := (𝟭 (HomotopyCategory.Plus C)).totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  have : IsIso (DerivedCategory.Plus.Qh.map s) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) s hs
  have : IsIso ((DerivedCategory.Plus.Qh ⋙ (𝟭 (HomotopyCategory.Plus C)).totalRightDerived
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).map s) := by
    rw [Functor.comp_map]
    infer_instance
  have : IsIso (s ≫ α.app Y) := by
    rw [show s ≫ α.app Y = α.app X ≫ _ from α.naturality s]
    infer_instance
  exact IsIso.of_isIso_comp_right s (α.app Y)

/-- If `𝒜` has enough injectives, then for every additive `F : 𝒜 ⥤ ℬ` the right derived functor
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined: the right derived functor of `K⁺(F) ⋙ Q⁺_ℬ`
relative to the quasi-isomorphisms of `K⁺(𝒜)` is defined at every object of `K⁺(𝒜)`. Every
bounded below complex is quasi-isomorphic to a bounded below complex of injectives, and `K⁺(F)`
sends a quasi-isomorphism between two of these to an isomorphism, so [Stacks, Tag 06XN] applies. -/
theorem isRightDerivable_mapHomotopyCategoryPlus_comp_Qh :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C) := by
  have hS := quasiIsoPlus_isSaturated (C := C)
  have := hS.hasLeftCalculusOfFractions
  refine (Stacks.DerivedFunctor.Computing.rightDerived_everywhereDefined_and_computes _ _
    hS.isSaturatedMultiplicative {K | ∀ n : ℤ, Injective (K.obj.as.X n)} (fun X ↦ ?_)
    (fun X Y s hs hX hY ↦ ?_)).1
  · let r : (HomotopyCategory.Plus.localizerMorphism C).RightResolution X := Classical.arbitrary _
    exact ⟨_, r.w, r.hw, fun _ ↦ inferInstance⟩
  · have : ∀ n : ℤ, Injective (X.obj.as.X n) := hX
    have : ∀ n : ℤ, Injective (Y.obj.as.X n) := hY
    have := isIso_of_quasiIso_of_injective s hs
    infer_instance

/-- With enough injectives, the higher right derived functor `R ⁱ F` of [Stacks, Tag 015A],
defined from the everywhere defined `RF`, is the functor
`CategoryTheory.Functor.rightDerivedPlus` constructed from injective resolutions. -/
theorem rightDerivedOfIsRightDerivable_eq_rightDerivedPlus
    (h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (i : ℤ) :
    F.rightDerivedOfIsRightDerivable h i = F.rightDerivedPlus i := by
  unfold rightDerivedOfIsRightDerivable rightDerivedFunctorPlusOfIsRightDerivable rightDerivedPlus
    rightDerivedFunctorPlus
  rfl

end EnoughInjectives

end CategoryTheory.Functor

end
