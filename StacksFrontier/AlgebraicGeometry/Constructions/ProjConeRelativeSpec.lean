module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecIsoOverU
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cone and the punctured cone as relative spectra over the projective spectrum

Let `A` be a nonnegatively graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached to
cone data `B` for `A`, with `U ⊆ L` the punctured cone, the part of `L` lying over
`X ∖ V(A₊)`. The projection `π` is affine, and so is its restriction to `U`; an affine morphism is
the structure morphism of the relative spectrum of the direct image of its structure sheaf, by the
criterion of [Stacks, Tag 01S8]. This file draws that consequence for the two morphisms:

  `L = Spec_P(π_* 𝒪_L)` and `U = Spec_P((π|_U)_* 𝒪_U)`,

as isomorphisms of schemes over `P`. These are the two presentations displayed in the diagram of
[Stacks, Tag 0EKG]; the two direct-image algebras are the ones of
`Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebra` and
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebra`, whose sections over a standard open
`D₊(f)` of `P` are the direct sums `⨁_{m ≥ 0} Γ(D₊(f), 𝒪_P(m))` respectively
`⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))` of sections of twisting sheaves, by
`Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsEquivTwistSections` and
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIso`: **the cone is, over `P`, the
  relative spectrum of its direct-image algebra**.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIso`: **the punctured cone is,
  over `P`, the relative spectrum of its direct-image algebra**.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIsoOpenU`: for the truncation
  algebra, **that relative spectrum is the open `U` of `X`**.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIsoOpenU`: the same
  statement with the algebra named as the twist algebra of [Stacks, Tag 01CF] itself,
  **`Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) = U`**, which is the equality on the left of the diagram.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIso_hom_left_comp` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIso_hom_left_comp`: the two
  isomorphisms lie over `P`, written out as equalities of morphisms of schemes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIsoOpenU_hom_comp_ι` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom_comp_ι`:
  the two identifications with `U` are ones over `X`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIso_hom`,
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIso_hom` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecIsoOpenU_hom`, with the
  companion `…_inv` statements: **each map of the diagram is the glued comparison morphism of
  `AlgebraicGeometry.toRelativeSpecOfAlgebraIso`**, so the diagram exhibits its maps rather than
  asserting that they exist.

## Implementation notes

The direct-image algebras are named here as `Stacks.AffineAlgebraEquivalence.pushforwardAlgebra`
of the respective morphisms rather than through `coneAlgebra` and `puncturedConeAlgebra`: the
quasi-coherence instance that the relative spectrum requires is stated for the former, and
instance search does not unfold the latter. The two are the same algebra sheaf, which is
`coneAlgebra_eq_pushforwardAlgebra` and `puncturedConeAlgebra_eq_pushforwardAlgebra`.

The two isomorphisms here hold for arbitrary cone data, so they can only name the direct-image
algebra: the twist algebras of [Stacks, Tag 01CF] are attached to the truncation cone and to
nothing else. For that cone the same two presentations are available with the algebra named as
the twist algebra itself, which is what the diagram of [Stacks, Tag 0EKG] displays:
`Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso` presents `L` as
`Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` and
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIso` presents the
punctured cone as `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`.

Affineness of the two morphisms is `Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi` and
`Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi_restrict`, which are theorems rather than
instances; they are made local instances here so that the relative spectra can be named in the
statements.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (c : ProjAndSpec.ConeData 𝒜 ℬ)

attribute [local instance] ProjAndSpec.isAffineHom_pi ProjAndSpec.isAffineHom_pi_restrict
  isQuasicoherent_pushforwardAlgebra

/-- The direct-image algebra of the cone is the pushforward algebra of the cone projection. -/
theorem coneAlgebra_eq_pushforwardAlgebra :
    coneAlgebra c = pushforwardAlgebra (ProjAndSpec.pi c) :=
  rfl

/-- The direct-image algebra of the punctured cone is the pushforward algebra of the restricted
cone projection. -/
theorem puncturedConeAlgebra_eq_pushforwardAlgebra :
    puncturedConeAlgebra c =
      pushforwardAlgebra ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c) :=
  rfl

/-- **`L = Spec_P(π_* 𝒪_L)`**: the cone is, over `P = Proj A`, the relative spectrum of its
direct-image algebra, the cone projection being affine. -/
@[stacks 0EKG "L is, over P, the relative spectrum of the direct-image algebra of the cone"]
def coneRelativeSpecIso :
    Over.mk (ProjAndSpec.pi c) ≅
      Over.mk (relativeSpecToBase (pushforwardAlgebra (ProjAndSpec.pi c))) :=
  relativeSpecPushforwardAlgebraIso (ProjAndSpec.pi c)

/-- **`U = Spec_P((π|_U)_* 𝒪_U)`**: the punctured cone is, over `P = Proj A`, the relative
spectrum of its direct-image algebra, the restricted cone projection being affine. -/
@[stacks 0EKG "the punctured cone is, over P, the relative spectrum of its direct-image algebra"]
def puncturedConeRelativeSpecIso :
    Over.mk ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c) ≅
      Over.mk (relativeSpecToBase
        (pushforwardAlgebra ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c))) :=
  relativeSpecPushforwardAlgebraIso ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)

/-- The identification of the cone with a relative spectrum is an identification over `P`. -/
theorem coneRelativeSpecIso_hom_left_comp :
    (coneRelativeSpecIso c).hom.left ≫
        relativeSpecToBase (pushforwardAlgebra (ProjAndSpec.pi c)) =
      ProjAndSpec.pi c :=
  Over.w (coneRelativeSpecIso c).hom

/-- The identification of the punctured cone with a relative spectrum is an identification over
`P`. -/
theorem puncturedConeRelativeSpecIso_hom_left_comp :
    (puncturedConeRelativeSpecIso c).hom.left ≫
        relativeSpecToBase
          (pushforwardAlgebra ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)) =
      (ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c :=
  Over.w (puncturedConeRelativeSpecIso c).hom

/-- **The two maps of the identification of the cone with a relative spectrum are exhibited**:
each is the morphism `AlgebraicGeometry.toRelativeSpecOfAlgebraIso` respectively
`AlgebraicGeometry.fromRelativeSpecOfAlgebraIso` glues over the standard opens of `P` out of the
identification of `π_* 𝒪_L` with itself. -/
theorem coneRelativeSpecIso_hom :
    (coneRelativeSpecIso c).hom =
      toRelativeSpecOfAlgebraIso (ProjAndSpec.pi c)
        (pushforwardAlgebra (ProjAndSpec.pi c)) (Iso.refl _) :=
  rfl

/-- The inverse of the identification of the cone with a relative spectrum is the morphism
`AlgebraicGeometry.fromRelativeSpecOfAlgebraIso` glues out of the identification of `π_* 𝒪_L`
with itself. -/
theorem coneRelativeSpecIso_inv :
    (coneRelativeSpecIso c).inv =
      fromRelativeSpecOfAlgebraIso (ProjAndSpec.pi c)
        (pushforwardAlgebra (ProjAndSpec.pi c)) (Iso.refl _) :=
  rfl

/-- **The two maps of the identification of the punctured cone with a relative spectrum are
exhibited** in the same way. -/
theorem puncturedConeRelativeSpecIso_hom :
    (puncturedConeRelativeSpecIso c).hom =
      toRelativeSpecOfAlgebraIso ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)
        (pushforwardAlgebra ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)) (Iso.refl _) :=
  rfl

/-- The inverse of the identification of the punctured cone with a relative spectrum is the
morphism `AlgebraicGeometry.fromRelativeSpecOfAlgebraIso` glues out of the identification of
`(π|_U)_* 𝒪_U` with itself. -/
theorem puncturedConeRelativeSpecIso_inv :
    (puncturedConeRelativeSpecIso c).inv =
      fromRelativeSpecOfAlgebraIso ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)
        (pushforwardAlgebra ((ProjAndSpec.openUInL c).ι ≫ ProjAndSpec.pi c)) (Iso.refl _) :=
  rfl

/-! ### The punctured cone of the truncation algebra is the open `U` of `X` -/

section Truncation

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The forward map of `e.symm ≪≫ asIso g`, followed by `ι`, is `e.inv` followed by `g ≫ ι`. -/
private theorem symm_trans_asIso_hom_comp {X Y Z W : Scheme} {e : X ≅ Y} {g : X ⟶ Z} {_ : IsIso g}
    {ι : Z ⟶ W} : (e.symm ≪≫ asIso g).hom ≫ ι = e.inv ≫ g ≫ ι := by
  simp

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- **The relative spectrum over `P` of the direct-image algebra of the punctured cone is the
open `U = X ∖ V(A₊)` of `X`**, for the truncation algebra. This is the equality on the left of the
diagram of [Stacks, Tag 0EKG]: the punctured cone is that relative spectrum, and `L ⟶ X` carries
it isomorphically onto `U`. -/
@[stacks 0EKG "the relative spectrum of the punctured cone's direct-image algebra is U",
  ega "II 8.12.5" "special case",
  ega "II 8.6.2" "special case"]
def puncturedConeRelativeSpecIsoOpenU :
    Stacks.AffineAlgebraEquivalence.relativeSpec
        (pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜)) ≅
      (ProjAndSpec.openU 𝒜).toScheme :=
  ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
      (puncturedConeRelativeSpecIso (truncationConeData 𝒜))).symm ≪≫
    @asIso _ _ _ _ (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) (isIso_toSpecA_restrict 𝒜)

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- The identification of the relative spectrum with `U` is one over `X`: followed by the
inclusion of `U` it is the structure morphism `L ⟶ X` read on the punctured cone. -/
@[ega "II 8.6.2" "Affine-base case"]
theorem puncturedConeRelativeSpecIsoOpenU_hom_comp_ι :
    (puncturedConeRelativeSpecIsoOpenU 𝒜).hom ≫ (ProjAndSpec.openU 𝒜).ι =
      ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
          (puncturedConeRelativeSpecIso (truncationConeData 𝒜))).inv ≫
        (openUInL 𝒜).ι ≫ toSpecA 𝒜 := by
  rw [openUInL_ι_comp_toSpecA]
  exact symm_trans_asIso_hom_comp

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- **The forward map of the identification of the relative spectrum with `U` is exhibited**: it
is the glued comparison morphism from the relative spectrum to the punctured cone, followed by
the restriction of the structure morphism `L ⟶ X` to `U`. Only the inverse of that last
restriction is unnamed, and it is an inverse of an exhibited morphism shown to be an
isomorphism in `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.isIso_toSpecA_restrict`. -/
theorem puncturedConeRelativeSpecIsoOpenU_hom :
    (puncturedConeRelativeSpecIsoOpenU 𝒜).hom =
      (fromRelativeSpecOfAlgebraIso ((openUInL 𝒜).ι ≫ pi 𝒜)
            (pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜)) (Iso.refl _)).left ≫
        (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) :=
  rfl

/-! ### The left equality of the diagram: `U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))` -/

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- **`Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) = U`**: the relative spectrum over `P = Proj A` of the algebra of
all integral twists is the open `U = X ∖ V(A₊)` of `X = Spec A`. This is the equality on the left
of the diagram of [Stacks, Tag 0EKG], with the algebra named as the twist algebra
`⨁_{m ∈ ℤ} 𝒪_P(m)` itself rather than as the direct image `(π|_U)_* 𝒪_U` it was computed from: the
punctured cone is that relative spectrum by
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIso`, and `L ⟶ X`
carries the punctured cone isomorphically onto `U` by
`Stacks.AlgebraicGeometry.ProjAndSpecTruncation.isIso_toSpecA_restrict`. -/
@[stacks 0EKG "the left equality: U is Spec_P of the integer twist algebra",
  ega "II 8.12.5" "special case",
  ega "II 8.6.2" "special case"]
def puncturedConeRelativeSpecTwistAlgebraIsoOpenU :
    Stacks.AffineAlgebraEquivalence.relativeSpec (integerTwistAlgebraSheaf 𝒜) ≅
      (ProjAndSpec.openU 𝒜).toScheme :=
  ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
      (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).symm ≪≫
    @asIso _ _ _ _ (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) (isIso_toSpecA_restrict 𝒜)

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- The left equality of the diagram is one over `X`: followed by the inclusion of `U` it is the
structure morphism `L ⟶ X` read on the punctured cone. -/
@[ega "II 8.6.2" "Affine-base case"]
theorem puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom_comp_ι :
    (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ (ProjAndSpec.openU 𝒜).ι =
      ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
          (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv ≫
        (openUInL 𝒜).ι ≫ toSpecA 𝒜 := by
  rw [openUInL_ι_comp_toSpecA]
  exact symm_trans_asIso_hom_comp

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation in
/-- **The forward map of the left equality is exhibited**: it is the morphism glued over the
standard opens of `P` out of the identification
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSheafIso` of `(π|_U)_* 𝒪_U` with the
integral twist algebra, followed by the restriction of the structure morphism `L ⟶ X` to `U`. -/
theorem puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom :
    (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom =
      (fromRelativeSpecOfAlgebraIso ((openUInL 𝒜).ι ≫ pi 𝒜) (integerTwistAlgebraSheaf 𝒜)
            (puncturedConeAlgebraSheafIso 𝒜).symm).left ≫
        (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) :=
  rfl

end Truncation

end Stacks.AlgebraicGeometry.ProjConeTwist

end
