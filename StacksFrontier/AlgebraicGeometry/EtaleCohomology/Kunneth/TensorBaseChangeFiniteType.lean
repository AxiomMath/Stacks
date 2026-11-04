module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType

/-!
# The canonical map of Tags 0F1J and 0F1N over a field

Let `K` be a field, `n ≥ 1` an integer invertible in `K`, and consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes of finite type over `K` with `X' = X ×_K S'` and `Y = X' ×_{S'} T`. [Stacks, Tag 0F1N]
asserts that the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism for all `E ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(T_étale, ℤ/nℤ)`.

The morphisms `g` and `h` are morphisms of schemes of finite type over `K`, so they are
quasi-compact and quasi-separated with `cd(g), cd(h) < ∞` ([Stacks, Tag 0F10] (1),
`AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_finiteType`). This is where
the source uses that the schemes are of finite type over `K`: it makes `Rg_*` and `Rh_*` commute
with direct sums ([Stacks, Tag 0F11] (1)), and
`Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isGE` then reduces the
statement to [Stacks, Tag 0F1J].

## Main results

* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_finiteType_of_isGE` —
  over a field and for schemes of finite type, the canonical map is invertible at all
  `p⁻¹E` and `F` once it is at `p⁻¹E` with `E ∈ D⁺` of Tor amplitude bounded below and `F ∈ D⁺`.
* `isIso_tensorBaseChangeMap_of_finiteType_of_hasTorAmplitudeGE` —
  the same at an arbitrary object `A` of `D(X'_étale, ℤ/nℤ)` in place of `p⁻¹E`.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_obj_of_finiteType_of_isGE`
  — the common form, at `P(E)` for a triangulated functor `P` commuting with direct sums.

## References

* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

-- [Stacks, Tag 0F10] imports `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

/-- Local finite type and quasi-compactness are stable under base change. -/
private theorem locallyOfFiniteType_and_quasiCompact_of_isPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D} (hP : IsPullback a b c d)
    [LocallyOfFiniteType c] [QuasiCompact c] : LocallyOfFiniteType b ∧ QuasiCompact b :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType) hP ‹_›,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) hP ‹_›⟩

/-- **The reduction to bounded below objects over a field, along an exact functor commuting with
direct sums.** Let `K` be a field, `n ≥ 1`, and let `h ≫ f' = e ≫ g` be a fibre square
(`Y = X' ×_{S'} T`) of schemes of finite type over `K` (through `πS`, `f' ≫ πS` and `g ≫ πS`).
Let `P : D(X_étale, ℤ/nℤ) ⥤ D(X'_étale, ℤ/nℤ)` be a triangulated functor commuting with countable
direct sums. If the canonical map `P(E) ⊗^L (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹P(E) ⊗^L e⁻¹F)` is invertible
for `E ∈ D⁺` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺`, it is invertible for all `E` and `F`.

`g` and `h` are morphisms of schemes of finite type over `K`, hence quasi-compact and
quasi-separated with `cd(g), cd(h) < ∞` by [Stacks, Tag 0F10] (1); with the torsion of `ℤ/nℤ`
this is what `isIso_tensorBaseChangeMap_obj_of_isGE` needs. -/
theorem isIso_tensorBaseChangeMap_obj_of_finiteType_of_isGE (K : Type u) [Field K] (n : ℕ)
    [NeZero n] {X X' Y S' T : Scheme.{u}} (πS : S' ⟶ Spec (.of K)) (f' : X' ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (g : T ⟶ S') [LocallyOfFiniteType πS] [QuasiCompact πS]
    [LocallyOfFiniteType (f' ≫ πS)] [QuasiCompact (f' ≫ πS)] [LocallyOfFiniteType (g ≫ πS)]
    [QuasiCompact (g ≫ πS)] (hY : IsPullback h e f' g)
    (P : DerivedModules (ULift.{u + 1} (ZMod n)) X ⥤ DerivedModules (ULift.{u + 1} (ZMod n)) X')
    [P.CommShift ℤ] [P.IsTriangulated] [PreservesColimitsOfShape (Discrete ℕ) P]
    (isIso_of_isGE : ∀ (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
      (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (a b c : ℤ), E.IsGE b →
      HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a → F.IsGE c →
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w (P.obj E) F))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w (P.obj E) F) := by
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g πS
  have : QuasiCompact g := quasiCompact_of_finiteType K (g ≫ πS) πS g
  have : QuasiSeparated g := quasiSeparated_of_finiteType K (g ≫ πS) g
  obtain ⟨_, _⟩ := locallyOfFiniteType_and_quasiCompact_of_isPullback hY.flip
  have : QuasiSeparated h := quasiSeparated_of_finiteType K (h ≫ f' ≫ πS) h
  exact isIso_tensorBaseChangeMap_obj_of_isGE _ f' g h e hY.w
    (Hom.etaleCohomologicalDimension_lt_top_of_finiteType K (g ≫ πS) πS g rfl)
    (Hom.etaleCohomologicalDimension_lt_top_of_finiteType K (h ≫ f' ≫ πS) (f' ≫ πS) h
      (Category.assoc _ _ _).symm)
    (isTorsion_ulift_zmod n) P isIso_of_isGE E F

/-- **[Stacks, Tag 0F1N] from [Stacks, Tag 0F1J], over a field.** Let `K` be a field and `n ≥ 1`
an integer. Consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes of finite type over `K` (through `πX`, `πS` and `g ≫ πS`) with `X' = X ×_K S'` and
`Y = X' ×_{S'} T`. If the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is invertible for `E ∈ D⁺(X_étale, ℤ/nℤ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, ℤ/nℤ)`
(`isIso_of_isGE_of_hasTorAmplitudeGE`, the conclusion of [Stacks, Tag 0F1J] at this diagram),
then it is invertible for all `E ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(T_étale, ℤ/nℤ)`.

Not registered: the conclusion of [Stacks, Tag 0F1J] is an explicit argument. Every other input is
proved; the invertibility of `n` in `K` is needed only for that argument.

`g` and `h` are morphisms of schemes of finite type over `K`, hence quasi-compact and
quasi-separated with `cd(g), cd(h) < ∞` by [Stacks, Tag 0F10] (1); with the torsion of `ℤ/nℤ`
this is what `isIso_tensorBaseChangeMap_of_isGE` needs. -/
theorem isIso_tensorBaseChangeMap_of_finiteType_of_isGE (K : Type u) [Field K] (n : ℕ) [NeZero n]
    {X X' Y S' T : Scheme.{u}} (πX : X ⟶ Spec (.of K)) (πS : S' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [LocallyOfFiniteType πX]
    [QuasiCompact πX] [LocallyOfFiniteType πS] [QuasiCompact πS] [LocallyOfFiniteType (g ≫ πS)]
    [QuasiCompact (g ≫ πS)] (hX' : IsPullback p f' πX πS) (hY : IsPullback h e f' g)
    (isIso_of_isGE_of_hasTorAmplitudeGE : ∀ (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
      (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (a b c : ℤ), E.IsGE b →
      HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a → F.IsGE c →
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
        ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  obtain ⟨_, _⟩ := locallyOfFiniteType_and_quasiCompact_of_isPullback hX'
  exact isIso_tensorBaseChangeMap_obj_of_finiteType_of_isGE K n πS f' h e g hY _
    isIso_of_isGE_of_hasTorAmplitudeGE E F

/-- **The reduction to bounded below objects over a field, at an arbitrary object of
`D(X'_étale, ℤ/nℤ)`.** Let `K` be a field, `n ≥ 1`, and let `h ≫ f' = e ≫ g` be a fibre square
(`Y = X' ×_{S'} T`) of schemes of finite type over `K`. If the canonical map
`A ⊗^L (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L e⁻¹F)` is invertible for `A ∈ D⁺(X'_étale, ℤ/nℤ)` of Tor
amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, ℤ/nℤ)`, it is invertible for all `A` and `F`. This is
`isIso_tensorBaseChangeMap_obj_of_finiteType_of_isGE` at the identity functor; it is the form
used with `p = 𝟙 X`, where `p⁻¹` is not literally the identity. -/
theorem isIso_tensorBaseChangeMap_of_finiteType_of_hasTorAmplitudeGE (K : Type u) [Field K]
    (n : ℕ) [NeZero n] {X' Y S' T : Scheme.{u}} (πS : S' ⟶ Spec (.of K)) (f' : X' ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [LocallyOfFiniteType πS] [QuasiCompact πS]
    [LocallyOfFiniteType (f' ≫ πS)] [QuasiCompact (f' ≫ πS)] [LocallyOfFiniteType (g ≫ πS)]
    [QuasiCompact (g ≫ πS)] (hY : IsPullback h e f' g)
    (isIso_of_isGE : ∀ (A : DerivedModules (ULift.{u + 1} (ZMod n)) X')
      (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (a b c : ℤ), A.IsGE b →
      HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) A a → F.IsGE c →
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w A F))
    (A : DerivedModules (ULift.{u + 1} (ZMod n)) X')
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w A F) :=
  isIso_tensorBaseChangeMap_obj_of_finiteType_of_isGE (X := X') K n πS f' h e g hY (𝟭 _)
    isIso_of_isGE A F

end Stacks.EtaleCohomology.EtaleCoefficients
