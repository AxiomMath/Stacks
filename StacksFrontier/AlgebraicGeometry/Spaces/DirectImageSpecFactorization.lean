module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S`.  Then
`f_* 𝒪_Y` is a quasi-coherent `𝒪_X`-algebra (Stacks 03M9), and `f` factors canonically as
`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X` (Stacks 081X).

## Main definitions

* `AlgebraicGeometry.Space.directImageSpec`: the relative spectrum
  `\underline{Spec}_X(f_* 𝒪_Y)`, an algebraic space affine over `X`, and
  `AlgebraicGeometry.Space.directImageSpecIso` its identification of direct images.
* `AlgebraicGeometry.Space.toDirectImageSpec`: the canonical morphism
  `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`.

## Main results

* `AlgebraicGeometry.Space.directImageSpec_factorization`: `f_* 𝒪_Y` is quasi-coherent, and `f`
  factors as `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X` through the canonical morphism (Stacks 081X).

## Implementation notes

**The corrected form.**  The relative spectrum is
`AlgebraicGeometry.Space.boundedRelativeSpec`, defined for quasi-coherent algebras whose sections
over every étale chart are fewer than the cutoff of the big fppf site: the unbounded form of
Stacks 081V is refuted in this development by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`,
since algebraic spaces live on a site with a cardinal cutoff while algebra sheaves do not.  The
size condition costs nothing here: `f_* 𝒪_Y` satisfies it for *every* morphism `f`
(`AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra`), so it is proved, not assumed.

**Canonicity.**  Stacks obtains the morphism from the counit `f^* f_* 𝒪_Y ⟶ 𝒪_Y` through the
anti-equivalence over `Y`.  Through `AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`,
`Hom_X(Y, \underline{Spec}_X(𝒜)) = Hom_{𝒪_X}(𝒜, f_* 𝒪_Y)`, and the transpose of that counit is the
identity of `f_* 𝒪_Y`; so the canonical morphism is the unique morphism over `X` whose
direct-image map is the identification `\underline{Spec}_X(f_* 𝒪_Y)_* 𝒪 ≅ f_* 𝒪_Y`, which is how
`AlgebraicGeometry.Space.toDirectImageSpec` is defined and characterized.

## References

* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)`** of the direct image of `𝒪_Y` along a
quasi-compact, quasi-separated morphism, as an algebraic space affine over `X`. -/
def directImageSpec : AffineOver B S hS X :=
  boundedRelativeSpec B S hS
    (directImageAlgebra B S hS f (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs))
    (sectionsBelowCutoff_pushforwardAlgebra B S hS (Over.mk f))

/-- The direct image of the structure sheaf of `\underline{Spec}_X(f_* 𝒪_Y)` is `f_* 𝒪_Y`. -/
def directImageSpecIso :
    pushforwardAlgebra B S hS (directImageSpec B S hS f hfqc hfqs).obj ≅
      pushforwardAlgebra B S hS (Over.mk f) :=
  pushforwardAlgebraBoundedRelativeSpecIso B S hS
    (directImageAlgebra B S hS f (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs))
    (sectionsBelowCutoff_pushforwardAlgebra B S hS (Over.mk f))

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`**: the unique morphism over
`X` whose direct-image map is `AlgebraicGeometry.Space.directImageSpecIso`. -/
def toDirectImageSpec : Over.mk f ⟶ (directImageSpec B S hS f hfqc hfqs).obj :=
  overHomOfPushforwardAlgebraIso B S hS (directImageSpecIso B S hS f hfqc hfqs)

/-- **The canonical factorization through the relative spectrum of `f_* 𝒪_Y`.**  Let `f : Y ⟶ X`
be a quasi-compact, quasi-separated morphism of algebraic spaces.  Then `f_* 𝒪_Y` is a
quasi-coherent `𝒪_X`-algebra, and `f` factors as `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X` through
the canonical morphism `AlgebraicGeometry.Space.toDirectImageSpec`, which is the unique morphism
over `X` whose direct-image map is the identification `\underline{Spec}_X(f_* 𝒪_Y)_* 𝒪 ≅ f_* 𝒪_Y`.

The relative spectrum is the bounded one of `AlgebraicGeometry.Space.boundedRelativeSpec`: the
unbounded form of Stacks 081V is refuted here by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`, and
the size condition it needs is proved for `f_* 𝒪_Y` by
`AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra`. -/
@[stacks 081X "corrected (bounded) form: quasi-coherence of f_* 𝒪_Y, the factorization \
Y → Spec_X(f_* 𝒪_Y) → X, and its canonicity", sga "3 VIB 11.1" "partial"]
theorem directImageSpec_factorization :
    (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent ∧
      (toDirectImageSpec B S hS f hfqc hfqs).left ≫ (directImageSpec B S hS f hfqc hfqs).obj.hom =
        f ∧
      ∀ g : Over.mk f ⟶ (directImageSpec B S hS f hfqc hfqs).obj,
        g = toDirectImageSpec B S hS f hfqc hfqs ↔
          pushforwardAlgebraMap B S hS g = (directImageSpecIso B S hS f hfqc hfqs).hom :=
  ⟨isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs,
    Over.w (toDirectImageSpec B S hS f hfqc hfqs),
    fun g => eq_overHomOfPushforwardAlgebraIso_iff B S hS _ g⟩

/-- The canonical morphism induces an isomorphism `\underline{Spec}_X(f_* 𝒪_Y)_* 𝒪 ⟶ f_* 𝒪_Y` of
sheaves of rings. -/
instance isIso_pushforwardRingMap_toDirectImageSpec :
    IsIso (pushforwardRingMap B S hS (toDirectImageSpec B S hS f hfqc hfqs)) :=
  isIso_pushforwardRingMap_overHomOfPushforwardAlgebraIso B S hS _

end AlgebraicGeometry.Space

end
