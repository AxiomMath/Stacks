module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.GradedDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for the homogeneous pieces of `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a cartesian square of schemes with `g` flat, let `L` be an invertible `𝒪_X`-module, and let
`𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` be the graded `𝒪_S`-algebra of clause (5) of [Stacks, Tag 01VJ],
whose homogeneous pieces are `Stacks.RelativeAmple.gradedDirectImage`. This file proves that the
formation of each piece commutes with flat base change: the canonical morphism
`g^* f_* L^{⊗ d} ⟶ f'_* (g')^* L^{⊗ d}` is an isomorphism.

## Main definitions

* `Stacks.RelativeAmple.gradedDirectImageBaseChangeIso`: for `f` quasi-compact and
  quasi-separated, the isomorphism `g^* 𝒜_d ≅ 𝒜'_d`, where
  `𝒜' = ⨁_{d ≥ 0} (f')_* ((g')^* L)^{⊗ d}` is the graded algebra of the base change.
* `Stacks.RelativeAmple.gradedDirectImageBaseChangeIsoOfIsRelativelyAmple`: the same isomorphism
  for `L` ample relative to `f`.

## Main results

* `Stacks.RelativeAmple.pullback_pushforward_tensorPowModule`: the source of the base-change
  morphism at `L^{⊗ d}` is `g^* 𝒜_d`.
* `Stacks.RelativeAmple.isIso_baseChangeNatTrans_tensorPowModule`: for `f` quasi-compact and
  quasi-separated, the canonical base-change morphism is an isomorphism at every integral tensor
  power `L^{⊗ n}` of an invertible module.
* `Stacks.RelativeAmple.isIso_baseChangeNatTrans_gradedDirectImage`: the same for `L` ample
  relative to `f`, in every nonnegative degree.
* `Stacks.RelativeAmple.gradedDirectImageBaseChangeIso_hom`: the underlying morphism of
  `gradedDirectImageBaseChangeIso` is the canonical base-change morphism followed by the direct
  image of the comparison `(g')^* (L^{⊗ d}) ≅ ((g')^* L)^{⊗ d}`.

## References

* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.RelativeAmple

/-! ### The source of the base-change morphism is `g^* 𝒜_d` -/

/-- The pullback along `g` of the direct image of the tensor power `L^{⊗ d}` is the pullback of
the degree-`d` piece of `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`. -/
theorem pullback_pushforward_tensorPowModule {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (d : ℕ) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj (tensorPowModule X L (d : ℤ)))
      = (Scheme.Modules.pullback g).obj (gradedDirectImage f L (d : ℤ)) :=
  rfl

/-! ### Flat base change for the tensor powers, and for the pieces of `𝒜` -/

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
  (L : X.Modules) [IsInvertibleModule X L]

/-- **Flat base change for the direct image of a tensor power of an invertible module.** Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a cartesian square of schemes with `g` flat and `f` quasi-compact and quasi-separated, and let
`L` be an invertible `𝒪_X`-module. Then the canonical base-change morphism
`g^* f_* L^{⊗ n} ⟶ f'_* (g')^* L^{⊗ n}` is an isomorphism, for every integer `n`. -/
@[sga "3 VIB 11.0" "Clause (c), special case", sga "7 VII 1.3.8" "more general"]
theorem isIso_baseChangeNatTrans_tensorPowModule (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (n : ℤ) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
      (tensorPowModule X L n)) := by
  have : (tensorPowModule X L n).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L n
  exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H
    (tensorPowModule X L n)

/-- **The homogeneous pieces of `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` commute with flat base change**, for
`L` ample relative to `f`. For a cartesian square as above with `g` flat and `L` relatively
ample, the canonical base-change morphism `g^* 𝒜_d ⟶ f'_* (g')^* L^{⊗ d}` is an isomorphism for
every `d ≥ 0`. -/
theorem isIso_baseChangeNatTrans_gradedDirectImage (H : IsPullback g' f' f g) [Flat g]
    (hL : IsRelativelyAmple f L) (d : ℕ) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
      (tensorPowModule X L (d : ℤ))) := by
  have := hL.quasiCompact
  have := hL.quasiSeparated
  exact isIso_baseChangeNatTrans_tensorPowModule L H (d : ℤ)

/-! ### The pieces of `𝒜` and of the graded algebra of the base change -/

/-- **The formation of `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` commutes with flat base change, degreewise**:
for a cartesian square as above with `g` flat and `f` quasi-compact and quasi-separated,
`g^* 𝒜_d ≅ 𝒜'_d` for every `d ≥ 0`, where `𝒜' = ⨁_{d ≥ 0} (f')_* ((g')^* L)^{⊗ d}` is the graded
algebra built on `X'` from the pulled-back module `(g')^* L`. It is the canonical base-change
morphism `g^* f_* L^{⊗ d} ⟶ (f')_* (g')^* L^{⊗ d}` followed by the direct image along `f'` of the
isomorphism `(g')^* (L^{⊗ d}) ≅ ((g')^* L)^{⊗ d}`. -/
def gradedDirectImageBaseChangeIso (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (d : ℕ) :
    (Scheme.Modules.pullback g).obj (gradedDirectImage f L (d : ℤ)) ≅
      gradedDirectImage f' ((Scheme.Modules.pullback g').obj L) (d : ℤ) :=
  @asIso _ _ _ _ _ (isIso_baseChangeNatTrans_tensorPowModule L H (d : ℤ)) ≪≫
    (Scheme.Modules.pushforward f').mapIso
      (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso g' L
        (d : ℤ))

/-- The isomorphism `gradedDirectImageBaseChangeIso` is the canonical base-change morphism
followed by the direct image of the comparison of the pullback of a tensor power with the tensor
power of the pullback. -/
@[simp]
theorem gradedDirectImageBaseChangeIso_hom (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (d : ℕ) :
    (gradedDirectImageBaseChangeIso L H d).hom =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
          (tensorPowModule X L (d : ℤ)) ≫
        (Scheme.Modules.pushforward f').map
          (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso g' L
            (d : ℤ)).hom :=
  rfl

/-- **The formation of `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` commutes with flat base change, degreewise**,
for `L` ample relative to `f`: for a cartesian square as above with `g` flat,
`g^* 𝒜_d ≅ 𝒜'_d` for every `d ≥ 0`. -/
def gradedDirectImageBaseChangeIsoOfIsRelativelyAmple (H : IsPullback g' f' f g) [Flat g]
    (hL : IsRelativelyAmple f L) (d : ℕ) :
    (Scheme.Modules.pullback g).obj (gradedDirectImage f L (d : ℤ)) ≅
      gradedDirectImage f' ((Scheme.Modules.pullback g').obj L) (d : ℤ) :=
  haveI := hL.quasiCompact
  haveI := hL.quasiSeparated
  gradedDirectImageBaseChangeIso L H d

end Stacks.RelativeAmple

end
