module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two out of three along a long exact sequence, and the second step of [Stacks, Tag 02O5]

Let `E` be a cohomological `δ`-functor from an abelian category `𝒜` to an abelian category `ℬ`
([Stacks, Tag 010Q], `CategoryTheory.DeltaFunctor`) and let `P` be a weak Serre subcategory of
`ℬ` ([Stacks, Tag 0754], `CategoryTheory.ObjectProperty.IsWeakSerreClass`). For a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `𝒜`, write `Q(Xᵢ)` for *"`Eⁿ(Xᵢ)` lies in `P` for every
`n`"*. Then `Q` holds for any one of the three terms as soon as it holds for the other two:
each `Eⁿ(Xᵢ)` is the middle term of a five term exact subsequence of

`0 ⟶ E⁰(X₁) ⟶ E⁰(X₂) ⟶ E⁰(X₃) ⟶ E¹(X₁) ⟶ E¹(X₂) ⟶ ⋯`

whose other four terms are among the hypotheses, and `P.prop_obj₂_of_exact` is exactly the
defining property of a weak Serre subcategory in [Stacks, Tag 02MO] (2).

Specialised to `E = R ⁱ f_*` and `P =` coherence (a weak Serre subcategory by
`SheafOfModules.coherentModules_isWeakSerreClass`, [Stacks, Tag 01BY] (5)), this is the second
paragraph of the proof of [Stacks, Tag 02O5].

## Main results

* `CategoryTheory.DeltaFunctor.prop_obj_X₃`, `….prop_obj_X₁`, `….prop_obj_X₂`: the three
  implications, for an arbitrary `δ`-functor and an arbitrary weak Serre subcategory.
* `CategoryTheory.DeltaFunctor.prop_obj_twoOutOfThree`: the three together, in the shape a
  dévissage consumes.
* `Stacks.AlgebraicGeometry.CoherentTwoOutOfThree.isWeakSerreClass_isCoherent`: coherence as a
  weak Serre subcategory of `X.Modules`.
* `Stacks.AlgebraicGeometry.CoherentTwoOutOfThree.forall_isCoherent_rightDerived_X₃`,
  `….forall_isCoherent_rightDerived_X₁`, `….forall_isCoherent_rightDerived_X₂`: the second
  paragraph of the proof of [Stacks, Tag 02O5], for an arbitrary morphism of schemes.
* `….forall_isCoherent_rightDerived_twoOutOfThree`: the three together.

## Implementation notes

This file does not prove [Stacks, Tag 02O5]: every statement assumes coherence of the higher
direct images for two of the three terms of a short exact sequence and concludes it for the
third, so no tag is registered here.

The degree-zero cases are not instances of the five term argument: `E⁰(X₁)` is a kernel of
`E⁰(X₂) ⟶ E⁰(X₃)` by `mono_map_f`, and for `E⁰(X₂)` the sequence is padded on the left by the
zero object, which `P` contains.

`AlgebraicGeometry.Scheme.Modules` is a definition for `SheafOfModules X.ringCatSheaf` with its
own `Category` and `Abelian` instances, and instance search does not find
`SheafOfModules.coherentModules_isWeakSerreClass` at `X.Modules`;
`isWeakSerreClass_isCoherent` is the same term with the `X.Modules` type declared.

The coherence predicate is `_root_.SheafOfModules.IsCoherent` ([Stacks, Tag 01BV]), bridged to
`Stacks.SheafOfModules.IsCoherent` by `SheafOfModules.isCoherent_iff`.

Only the existence of a `δ` making the long sequence exact is used, so the `δ`-functor is built
inside the proofs and the statements mention only `Functor.rightDerived`.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  (E : DeltaFunctor A B) (P : ObjectProperty B) [P.IsWeakSerreClass] {S : ShortComplex A}

/-- Two out of three, the third term: if every `Eⁿ(X₁)` and every `Eⁿ(X₂)` lies in the weak
Serre subcategory `P`, then so does every `Eⁿ(X₃)`: it is the middle term of the exact
`Eⁿ(X₁) ⟶ Eⁿ(X₂) ⟶ Eⁿ(X₃) ⟶ Eⁿ⁺¹(X₁) ⟶ Eⁿ⁺¹(X₂)`. -/
theorem prop_obj_X₃ (hS : S.ShortExact)
    (h₁ : ∀ n : ℕ, P ((E.functor n).obj S.X₁)) (h₂ : ∀ n : ℕ, P ((E.functor n).obj S.X₂))
    (n : ℕ) : P ((E.functor n).obj S.X₃) :=
  ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
    (f₀ := (E.functor n).map S.f) (f₁ := (E.functor n).map S.g) (f₂ := E.δ hS n)
    (f₃ := (E.functor (n + 1)).map S.f)
    (E.map_f_comp_map_g n) (E.map_g_δ hS n) (E.δ_map_f hS n)
    (E.exact_map hS n) (E.exact_δ₁ hS n) (E.exact_δ₂ hS n)
    (h₁ n) (h₂ n) (h₁ (n + 1)) (h₂ (n + 1))

/-- Two out of three, the first term: if every `Eⁿ(X₂)` and every `Eⁿ(X₃)` lies in the weak
Serre subcategory `P`, then so does every `Eⁿ(X₁)`. -/
theorem prop_obj_X₁ (hS : S.ShortExact)
    (h₂ : ∀ n : ℕ, P ((E.functor n).obj S.X₂)) (h₃ : ∀ n : ℕ, P ((E.functor n).obj S.X₃))
    (n : ℕ) : P ((E.functor n).obj S.X₁) := by
  cases n with
  | zero =>
    have hm : Mono (S.map (E.functor 0)).f := E.mono_map_f hS
    exact P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel ((E.functor 0).map S.g))
        (E.exact_map hS 0).fIsKernel)
      (P.prop_kernel _ (h₂ 0) (h₃ 0))
  | succ m =>
    exact ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
      (f₀ := (E.functor m).map S.g) (f₁ := E.δ hS m) (f₂ := (E.functor (m + 1)).map S.f)
      (f₃ := (E.functor (m + 1)).map S.g)
      (E.map_g_δ hS m) (E.δ_map_f hS m) (E.map_f_comp_map_g (m + 1))
      (E.exact_δ₁ hS m) (E.exact_δ₂ hS m) (E.exact_map hS (m + 1))
      (h₂ m) (h₃ m) (h₂ (m + 1)) (h₃ (m + 1))

/-- Two out of three, the middle term: if every `Eⁿ(X₁)` and every `Eⁿ(X₃)` lies in the weak
Serre subcategory `P`, then so does every `Eⁿ(X₂)`. -/
theorem prop_obj_X₂ (hS : S.ShortExact)
    (h₁ : ∀ n : ℕ, P ((E.functor n).obj S.X₁)) (h₃ : ∀ n : ℕ, P ((E.functor n).obj S.X₃))
    (n : ℕ) : P ((E.functor n).obj S.X₂) := by
  cases n with
  | zero =>
    have hm : Mono ((E.functor 0).map S.f) := E.mono_map_f hS
    have hm' : Mono (ShortComplex.mk (0 : (0 : B) ⟶ (E.functor 0).obj S.X₁)
      ((E.functor 0).map S.f) zero_comp).g := hm
    exact ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
      (f₀ := (0 : (0 : B) ⟶ (E.functor 0).obj S.X₁)) (f₁ := (E.functor 0).map S.f)
      (f₂ := (E.functor 0).map S.g) (f₃ := E.δ hS 0)
      zero_comp (E.map_f_comp_map_g 0) (E.map_g_δ hS 0)
      ((ShortComplex.exact_iff_mono _ rfl).2 hm') (E.exact_map hS 0) (E.exact_δ₁ hS 0)
      P.prop_zero (h₁ 0) (h₃ 0) (h₁ 1)
  | succ m =>
    exact ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
      (f₀ := E.δ hS m) (f₁ := (E.functor (m + 1)).map S.f) (f₂ := (E.functor (m + 1)).map S.g)
      (f₃ := E.δ hS (m + 1))
      (E.δ_map_f hS m) (E.map_f_comp_map_g (m + 1)) (E.map_g_δ hS (m + 1))
      (E.exact_δ₂ hS m) (E.exact_map hS (m + 1)) (E.exact_δ₁ hS (m + 1))
      (h₃ m) (h₁ (m + 1)) (h₃ (m + 1)) (h₁ (m + 2))

/-- The two-out-of-three property of a weak Serre subcategory along a `δ`-functor: all three
implications together. -/
theorem prop_obj_twoOutOfThree (hS : S.ShortExact) :
    (((∀ n : ℕ, P ((E.functor n).obj S.X₁)) ∧ ∀ n : ℕ, P ((E.functor n).obj S.X₂)) →
        ∀ n : ℕ, P ((E.functor n).obj S.X₃)) ∧
      (((∀ n : ℕ, P ((E.functor n).obj S.X₁)) ∧ ∀ n : ℕ, P ((E.functor n).obj S.X₃)) →
          ∀ n : ℕ, P ((E.functor n).obj S.X₂)) ∧
        (((∀ n : ℕ, P ((E.functor n).obj S.X₂)) ∧ ∀ n : ℕ, P ((E.functor n).obj S.X₃)) →
            ∀ n : ℕ, P ((E.functor n).obj S.X₁)) :=
  ⟨fun h => E.prop_obj_X₃ P hS h.1 h.2, fun h => E.prop_obj_X₂ P hS h.1 h.2,
    fun h => E.prop_obj_X₁ P hS h.1 h.2⟩

end CategoryTheory.DeltaFunctor

namespace Stacks.AlgebraicGeometry.CoherentTwoOutOfThree

attribute [local instance] HasDerivedCategory.standard

/-- Coherent modules form a weak Serre subcategory of `X.Modules`. -/
@[sga "6 IV 2.4" "special case"]
instance isWeakSerreClass_isCoherent (X : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass
      (fun M : X.Modules => _root_.SheafOfModules.IsCoherent M) :=
  _root_.SheafOfModules.coherentModules_isWeakSerreClass

/-- The long exact sequence of the higher direct images along `f`, as the cohomological
`δ`-functor of [Stacks, Tag 010Q]. There is no hypothesis on `f`. -/
private noncomputable def pushforwardDeltaFunctor {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) : CategoryTheory.DeltaFunctor X.Modules Y.Modules :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (AlgebraicGeometry.Scheme.Modules.pushforward f)

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {T : ShortComplex X.Modules}

/-- Write `𝒫(ℱ)` for "`R ᵖ f_* ℱ` is coherent for every `p`". For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `X`, `𝒫(ℱ₁)` and `𝒫(ℱ₂)` give `𝒫(ℱ₃)`. -/
theorem forall_isCoherent_rightDerived_X₃ (hT : T.ShortExact)
    (h₁ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁))
    (h₂ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂))
    (n : ℕ) : _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃) :=
  (pushforwardDeltaFunctor f).prop_obj_X₃
    (fun M : Y.Modules => _root_.SheafOfModules.IsCoherent M) hT h₁ h₂ n

/-- With `𝒫` as in `forall_isCoherent_rightDerived_X₃`, `𝒫(ℱ₂)` and `𝒫(ℱ₃)` give `𝒫(ℱ₁)`. -/
theorem forall_isCoherent_rightDerived_X₁ (hT : T.ShortExact)
    (h₂ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂))
    (h₃ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃))
    (n : ℕ) : _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁) :=
  (pushforwardDeltaFunctor f).prop_obj_X₁
    (fun M : Y.Modules => _root_.SheafOfModules.IsCoherent M) hT h₂ h₃ n

/-- With `𝒫` as in `forall_isCoherent_rightDerived_X₃`, `𝒫(ℱ₁)` and `𝒫(ℱ₃)` give `𝒫(ℱ₂)`. -/
theorem forall_isCoherent_rightDerived_X₂ (hT : T.ShortExact)
    (h₁ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁))
    (h₃ : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃))
    (n : ℕ) : _root_.SheafOfModules.IsCoherent
      (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂) :=
  (pushforwardDeltaFunctor f).prop_obj_X₂
    (fun M : Y.Modules => _root_.SheafOfModules.IsCoherent M) hT h₁ h₃ n

/-- For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `X`, coherence of all the
higher direct images along `f` of any two of the three terms gives it for the third. -/
theorem forall_isCoherent_rightDerived_twoOutOfThree (hT : T.ShortExact) :
    (((∀ n : ℕ, _root_.SheafOfModules.IsCoherent
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁)) ∧
        ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂)) →
      ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
        (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃)) ∧
    ((((∀ n : ℕ, _root_.SheafOfModules.IsCoherent
            (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁)) ∧
          ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
            (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃)) →
        ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂)) ∧
      (((∀ n : ℕ, _root_.SheafOfModules.IsCoherent
            (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₂)) ∧
          ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
            (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₃)) →
        ∀ n : ℕ, _root_.SheafOfModules.IsCoherent
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj T.X₁))) :=
  (pushforwardDeltaFunctor f).prop_obj_twoOutOfThree
    (fun M : Y.Modules => _root_.SheafOfModules.IsCoherent M) hT

end Stacks.AlgebraicGeometry.CoherentTwoOutOfThree

end
