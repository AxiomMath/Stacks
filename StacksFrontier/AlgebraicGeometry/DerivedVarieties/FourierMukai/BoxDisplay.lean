module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionDisplay

/-!
# The box step of the display of Tag 0G0E

Let `k` be a field, let `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` be schemes over `k` with
projections `pr_1` and `pr_2` from `X ×_k Y`, let `K` be a kernel on `X ×_k Y`, let `ℰ` be an
`𝒪_X`-module and `𝒢` a quasi-coherent `𝒪_Y`-module.  The proof of [Stacks, Tag 0G0E] runs its
steps 1, 2 and 3 on the *display*

`H^i(X ×_k Y, K ⊗^𝐋 (ℰ ⊠ 𝒢)) = H^i(Y, Φ_K(ℰ) ⊗^𝐋 𝒢)`,

whose first equality rewrites the module `ℰ ⊠ 𝒢` of [Stacks, Tag 0G46] into the two derived
pullbacks it is assembled from and moves the kernel into the middle:

`K ⊗^𝐋 (ℰ ⊠ 𝒢)[0] ≅ (L pr_1^*ℰ[0] ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢[0]`.

That is what this file assembles, from the box comparison
`AlgebraicGeometry.derivedExternalTensorSingleIso` and the symmetric monoidal structure of
[Stacks, Tag 0FPB].  Its companion, the middle equality of the display, is the derived
projection formula of `FourierMukai/ProjectionDisplay.lean`; the two meet in
`AlgebraicGeometry.fourierMukaiDisplayIso` below.

## Main definitions

* `AlgebraicGeometry.dtenRearrangeIso` — `A ⊗^𝐋 (B ⊗^𝐋 C) ≅ (B ⊗^𝐋 A) ⊗^𝐋 C` on `D(𝒪_W)`, the
  associativity and commutativity constraints of [Stacks, Tag 0FPB] composed.
* `AlgebraicGeometry.kernelTensorBoxSingleIso` — **the box step of the display**,
  `K ⊗^𝐋 (ℰ ⊠ 𝒢)[0] ≅ (L pr_1^*ℰ[0] ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢[0]`.
* `AlgebraicGeometry.fourierMukaiDisplayIsoOfIsPerfect` — the same display for a quasi-coherent
  `𝒢` that is merely perfect in degree zero, which is the generality step 2 of the source's proof
  needs, its modules of zero-dimensional support being perfect on a regular scheme but not locally
  free.
* `AlgebraicGeometry.fourierMukaiDisplayIso` — **the display of [Stacks, Tag 0G0E] before taking
  cohomology**, `R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]) ≅ Φ_K(ℰ) ⊗^𝐋 𝒢[0]`, for a finite locally free
  `𝒢`: the box step followed by the projection-formula step.

## Implementation notes

*The model of the derived categories.*  `CategoryTheory.HasDerivedCategory.standard` is
activated as a local instance at high priority, as in `FourierMukai/Basic.lean`,
`FourierMukai/Composition.lean` and `FourierMukai/ProjectionDisplay.lean`: that is the model
`dpull`, `dpush`, `dtenLeft`, `dtenR`, `fourierMukai` and [Stacks, Tag 0B54] are available at.  The
priority is what makes the crossing happen: importing
`ExternalTensor/SingleComparison.lean` brings the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and
`CategoryTheory.SheafOfModules.hasDerivedCategory` into scope, and instance search would prefer
them at their default priority.  The box comparison itself takes its three models as binders —
see the implementation notes of `ExternalTensor/SingleComparison.lean` for why that is the only
crossing available, `HasDerivedCategory` carrying the localized category as data — so it is
read here at the standard model with no transport.

*Why the rearrangement is only associativity and commutativity.*  `dtenLeft W A` and `dtenR W A`
are the two partial applications of one bifunctor, which is the tensor product of the monoidal
structure `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` of [Stacks, Tag 0FPB]
on the nose, and that structure is symmetric by `canonicalDerivedSymmetric`.  So
`A ⊗ (B ⊗ C) ≅ (B ⊗ A) ⊗ C` is the inverse associator followed by the braiding whiskered on the
right, and nothing about the derived tensor product beyond those two constraints is used.

*No tag is registered here.*  Tags 0G46, 0G0A, 0FPB, 0B53 and 0B54 are registered where they are
proved, and Tag 0G0E's own clauses are statements about `D^b_Coh` under hypotheses on `X`, `Y`
and `K` that are not assumed below; what is here is one equality of its display, for an
arbitrary kernel over a field.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Rearranging a triple derived tensor product -/

/-- **`A ⊗^𝐋 (B ⊗^𝐋 C) ≅ (B ⊗^𝐋 A) ⊗^𝐋 C`** on `D(𝒪_W)`: the inverse of the associator of
[Stacks, Tag 0FPB] followed by its braiding, whiskered by `C` on the right. -/
def dtenRearrangeIso (W : Scheme.{u}) (A B C : DerivedCategory W.Modules) :
    (dtenLeft W A).obj ((dtenLeft W B).obj C) ≅ (dtenLeft W ((dtenR W A).obj B)).obj C :=
  letI : MonoidalCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  letI : SymmetricCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  (α_ A B C).symm ≪≫ whiskerRightIso (β_ A B) C

/-! ### The box step -/

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- **The box step of the display of [Stacks, Tag 0G0E]**:

`K ⊗^𝐋 (ℰ ⊠ 𝒢)[0] ≅ (L pr_1^*ℰ[0] ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢[0]`

for an arbitrary kernel `K` on `X ×_k Y`, an arbitrary `𝒪_X`-module `ℰ` and a quasi-coherent
`𝒪_Y`-module `𝒢`.

The external tensor product of [Stacks, Tag 0G46] placed in degree zero is the derived external
tensor product of [Stacks, Tag 0G0A] of the two modules placed in degree zero — that is
`AlgebraicGeometry.derivedExternalTensorSingleIso`, which is where the field and the
quasi-coherence of `𝒢` are used — and the kernel is then moved into the middle by
`AlgebraicGeometry.dtenRearrangeIso`. -/
def kernelTensorBoxSingleIso (K : DerivedCategory (Limits.pullback f g).Modules)
    (E : X.Modules) (G : Y.Modules) [G.IsQuasicoherent] :
    (dtenLeft (Limits.pullback f g) K).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
          (externalTensorProduct f g E G)) ≅
      (dtenLeft (Limits.pullback f g)
          ((dtenR (Limits.pullback f g) K).obj
            ((dpull (Limits.pullback.fst f g)).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj E)))).obj
        ((dpull (Limits.pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :=
  (dtenLeft (Limits.pullback f g) K).mapIso
      (derivedExternalTensorSingleIso k f g E G).symm ≪≫
    dtenRearrangeIso (Limits.pullback f g) K _ _

/-! ### The display -/

/-- **The display of [Stacks, Tag 0G0E], before taking cohomology**:

`R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]) ≅ Φ_K(ℰ) ⊗^𝐋_{𝒪_Y} 𝒢[0]`

for an arbitrary kernel `K` on `X ×_k Y`, an arbitrary `𝒪_X`-module `ℰ` and a finite locally
free `𝒪_Y`-module `𝒢`.  Taking `H^i` of both sides is the display's chain of equalities.

It is the box step `AlgebraicGeometry.kernelTensorBoxSingleIso` pushed forward along `pr_2`,
followed by the projection-formula step
`AlgebraicGeometry.fourierMukaiTensorSingleIso` inverted.  A finite locally free module is
quasi-coherent, which is the hypothesis the box step asks of `𝒢`. -/
def fourierMukaiDisplayIsoOfIsPerfect (K : DerivedCategory (Limits.pullback f g).Modules)
    (E : X.Modules) (G : Y.Modules) [G.IsQuasicoherent]
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g) K).obj
          ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
            (externalTensorProduct f g E G))) ≅
      (dtenLeft Y ((fourierMukai f g K).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj E))).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
  (dpush (Limits.pullback.snd f g)).mapIso (kernelTensorBoxSingleIso k f g K E G) ≪≫
    (fourierMukaiTensorSingleIsoOfIsPerfect f g K E G hG).symm

/-- **The display of [Stacks, Tag 0G0E], before taking cohomology**, for a finite locally free
`𝒢`: the case of `AlgebraicGeometry.fourierMukaiDisplayIsoOfIsPerfect` in which the perfectness
of `𝒢[0]` and the quasi-coherence of `𝒢` both come from finite local freeness. -/
def fourierMukaiDisplayIso (K : DerivedCategory (Limits.pullback f g).Modules)
    (E : X.Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g) K).obj
          ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
            (externalTensorProduct f g E G))) ≅
      (dtenLeft Y ((fourierMukai f g K).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj E))).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
  haveI := hG
  haveI : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree G
  fourierMukaiDisplayIsoOfIsPerfect k f g K E G
    (isPerfect_single_of_isFiniteLocallyFree' G hG)

end AlgebraicGeometry

end
