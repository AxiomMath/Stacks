module

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.CommRingSheafLiftIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistUngradedSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cone is the relative spectrum of the algebra of nonnegative twists

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra. `Stacks.AlgebraicGeometry.ProjConeTwist.coneUngradedSheafIso`
identifies `π_* 𝒪_L` with the ungraded realization of
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra` as sheaves of *rings*. **This file
carries that identification through the remaining plumbing** — commutativity, the lift to
`CommRingCat`, the structure morphism from `𝒪_P` and quasi-coherence — and arrives at the
presentation displayed in the diagram of [Stacks, Tag 0EKG]:

  `L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`,

an isomorphism of schemes over `P` naming the twist algebra itself rather than the direct image
`π_* 𝒪_L` it was computed from.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebraSheaf`: **the algebra of nonnegative
  twists as a sheaf of commutative `𝒪_P`-algebras**, the shape the relative spectrum consumes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSheafIso`: **`π_* 𝒪_L` is that algebra
  sheaf**, as sheaves of commutative `𝒪_P`-algebras.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso`: **`L` is, over `P`,
  the relative spectrum of the algebra of nonnegative twists.**

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.heq_nonnegTwistMul_comm`: the multiplication of the
  algebra of nonnegative twists is commutative on homogeneous local sections.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap_structureMap`: **the degreewise inclusions
  carry the structure map `r ↦ r · 1` of the ungraded realization to the pullback of functions
  along `π`**, which is what makes the identification one of *algebras* over `𝒪_P` and not merely
  of sheaves of rings.
* `Stacks.AlgebraicGeometry.ProjConeTwist.isQuasicoherent_nonnegTwistAlgebraSheaf`: the algebra
  sheaf is quasi-coherent, being isomorphic to the direct image of a structure sheaf along an
  affine morphism.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso_hom_left_comp`: the
  presentation lies over `P`.

## Implementation notes

Commutativity of the graded multiplication is the heterogeneous statement
`Stacks.RelativeSpec.gradedAlgebraSheaf` asks for: in a negative degree both products are the zero
section of a zero sheaf, and in nonnegative degrees both are the pointwise product of the values
in the fibres, so commutativity is `mul_comm` in the module fibre.

The structure-map computation is the only place where the two descriptions of the scalar action
have to be compared. On the twist side the structure map of the ungraded realization is `r ↦ r • 1`
by definition, the degreewise inclusions are `𝒪_P`-linear, and they are unital by
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap_one`; on the cone side the action of a section
of `𝒪_P` on a function on the cone is multiplication by its pullback along `π`, by definition of
the direct image of a sheaf of modules. So `r • 1` on the left is the pullback of `r` on the right,
with `mul_one` in between. From there the comparison of structure morphisms is the comparison on
sections, since every section of the ungraded realization is *locally* a sum of homogeneous ones
only after the structure map has already been handled: the structure morphism factors through the
sheafification unit, and `Stacks.toSheafify_sheafifyRingHom` is what lets the computation be made
before sheafifying.

The last step is `AlgebraicGeometry.relativeSpecIsoOfAlgebraIso`, the transport of the
relative-spectrum presentation of an affine morphism along an isomorphism of algebra sheaves;
affineness of `π` is `Stacks.AlgebraicGeometry.ProjAndSpec.isAffineHom_pi`, a theorem made a local
instance here as in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeRelativeSpec.lean`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime ProjAndSpec.isAffineHom_pi
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Commutativity of the graded multiplication -/

/-- **The multiplication of the algebra of nonnegative twists is commutative** on homogeneous
local sections. In a negative degree both products vanish; in nonnegative degrees both are the
pointwise product of the values in the module fibres. -/
@[stacks 0EKG "the multiplication of the nonnegative twist algebra is commutative on \
homogeneous local sections"]
theorem heq_nonnegTwistMul_comm (i j : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (nonnegTwistingSheaf 𝒜 i).val.obj U) (b : (nonnegTwistingSheaf 𝒜 j).val.obj U) :
    HEq ((nonnegTwistMul 𝒜 i j).app U a b) ((nonnegTwistMul 𝒜 j i).app U b a) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [nonnegTwistMul_eq_zero_of_neg_left 𝒜 hi U a b,
      nonnegTwistMul_eq_zero_of_neg_right 𝒜 hi U b a]
    exact nonneg_heq_zero 𝒜 (add_comm i j)
  rcases lt_or_ge j 0 with hj | hj
  · rw [nonnegTwistMul_eq_zero_of_neg_right 𝒜 hj U a b,
      nonnegTwistMul_eq_zero_of_neg_left 𝒜 hj U b a]
    exact nonneg_heq_zero 𝒜 (add_comm i j)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, by omega⟩
  refine twist_heq 𝒜 (add_comm (m : ℤ) (k : ℤ)) fun s => ?_
  show a.1 s * b.1 s = b.1 s * a.1 s
  exact mul_comm _ _

/-! ### The algebra of nonnegative twists as a sheaf of algebras over the structure sheaf -/

/-- **The algebra of nonnegative twists `⨁_{m ≥ 0} 𝒪_P(m)` as a sheaf of commutative
`𝒪_P`-algebras**, which is the shape the relative spectrum of [Stacks, Tag 01LM] takes as
input. Its sheaf of rings is the ungraded realization of [Stacks, Tag 01CF] and its structure
morphism is `r ↦ r · 1`. -/
@[stacks 0EKG "the nonnegative twist algebra as a sheaf of commutative algebras over the \
structure sheaf of P"]
def nonnegTwistAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf (AlgebraicGeometry.Proj 𝒜) :=
  Stacks.RelativeSpec.gradedAlgebraSheaf (AlgebraicGeometry.Proj 𝒜) (nonnegTwistAlgebra 𝒜)
    (heq_nonnegTwistMul_comm 𝒜)

/-! ### The structure morphism -/

/-- **The degreewise inclusions carry the structure map `r ↦ r · 1` of the ungraded realization
to the pullback of functions along `π`.** This is what makes the identification of `π_* 𝒪_L` with
the twist algebra one of algebras over `𝒪_P`, and not merely of sheaves of rings: the inclusions
are `𝒪_P`-linear and unital, and the action of a section of `𝒪_P` on a function on the cone is
multiplication by its pullback. -/
@[stacks 0EKG "the degreewise inclusions carry the structure map of the ungraded realization of \
the nonnegative twist algebra to the pullback of functions along the cone projection"]
theorem coneTotalMap_structureMap (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.obj (op U)) :
    coneTotalMap 𝒜 U ((nonnegTwistPresheafAlgebra 𝒜).structureMap (op U) r) =
      ((pi 𝒜).c.app (op U)).hom r := by
  have key : coneTotalMap 𝒜 U ((nonnegTwistPresheafAlgebra 𝒜).structureMap (op U) r) =
      (pi 𝒜).app U r * coneTotalMap 𝒜 U 1 :=
    map_smul (ConcreteCategory.hom ((coneTwistDirectSumHom 𝒜).app (op U))) r
      (1 : (nonnegTwistPresheafAlgebra 𝒜).Total (op U))
  rw [key, coneTotalMap_one, mul_one]

/-- The identification of `π_* 𝒪_L` with the ungraded realization, read on a section coming from
the presheaf: it is the degreewise inclusion. -/
theorem coneUngradedSheafIso_totalUnit (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (z : (nonnegTwistPresheafAlgebra 𝒜).Total U) :
    ((coneUngradedSheafIso 𝒜).hom.hom.app U).hom
        ((nonnegTwistPresheafAlgebra 𝒜).totalUnit
          (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) U z) =
      coneTotalMap 𝒜 U.unop z :=
  congrArg
    (fun φ : (nonnegTwistPresheafAlgebra 𝒜).totalPresheaf ⟶ (conePushforwardRingSheaf 𝒜).obj =>
      (φ.app U).hom z)
    (toSheafify_coneUngradedSheafIso_hom 𝒜)

/-! ### The identification of algebra sheaves, and the relative spectrum -/

/-- **`π_* 𝒪_L` is the algebra of nonnegative twists**, as sheaves of commutative
`𝒪_P`-algebras. -/
@[stacks 0EKG "the identification pi_* O_L = the nonnegative twist algebra, as sheaves of \
commutative algebras over the structure sheaf of P, for the cone of the truncation algebra"]
def coneAlgebraSheafIso :
    nonnegTwistAlgebraSheaf 𝒜 ≅ pushforwardAlgebra (pi 𝒜) :=
  Under.isoMk
    (Stacks.CommRingSheaf.isoMk (pushforwardAlgebra (pi 𝒜)).right
      ((nonnegTwistAlgebra 𝒜).mul_comm_ungradedSheaf (heq_nonnegTwistMul_comm 𝒜))
      (coneUngradedSheafIso 𝒜))
    (by
      refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
        (RingHom.ext fun r => ?_)))
      exact (coneUngradedSheafIso_totalUnit 𝒜 U
        ((nonnegTwistPresheafAlgebra 𝒜).structureMap U r)).trans
        (coneTotalMap_structureMap 𝒜 U.unop r))

/-- The algebra of nonnegative twists is a quasi-coherent sheaf of `𝒪_P`-algebras: it is the
direct image of the structure sheaf of the cone along the affine morphism `π`. -/
@[stacks 0EKG "the nonnegative twist algebra is a quasi-coherent sheaf of algebras over the \
structure sheaf of P"]
instance isQuasicoherent_nonnegTwistAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (nonnegTwistAlgebraSheaf 𝒜) :=
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso (coneAlgebraSheafIso 𝒜).symm
    (isQuasicoherent_pushforwardAlgebra (pi 𝒜))

/-- **`L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`**: the cone is, over `P = Proj A`, the relative spectrum of
the algebra of nonnegative twists. This is the presentation on the right of the diagram of
[Stacks, Tag 0EKG], with the algebra named as the twist algebra rather than as the direct image
`π_* 𝒪_L` it was computed from. -/
@[stacks 0EKG "L is, over P, the relative spectrum of the nonnegative twist algebra, for the \
cone of the truncation algebra", ega "II 8.7.3" "partial"]
def coneRelativeSpecTwistAlgebraIso :
    Over.mk (pi 𝒜) ≅ Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜)) :=
  relativeSpecIsoOfAlgebraIso (pi 𝒜) (nonnegTwistAlgebraSheaf 𝒜) (coneAlgebraSheafIso 𝒜).symm

/-- The presentation of the cone as a relative spectrum is one over `P`. -/
theorem coneRelativeSpecTwistAlgebraIso_hom_left_comp :
    (coneRelativeSpecTwistAlgebraIso 𝒜).hom.left ≫
        relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜) =
      pi 𝒜 :=
  Over.w (coneRelativeSpecTwistAlgebraIso 𝒜).hom

/-- **The map `L ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` of the diagram is exhibited**: it is the morphism
glued, over the standard opens of `P`, out of the identification
`Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSheafIso` of `π_* 𝒪_L` with the nonnegative
twist algebra. -/
theorem coneRelativeSpecTwistAlgebraIso_hom :
    (coneRelativeSpecTwistAlgebraIso 𝒜).hom =
      toRelativeSpecOfAlgebraIso (pi 𝒜) (nonnegTwistAlgebraSheaf 𝒜)
        (coneAlgebraSheafIso 𝒜).symm :=
  rfl

/-- **The map `Spec_P(⨁_{m ≥ 0} 𝒪_P(m)) ⟶ L` of the diagram is exhibited** in the same way. -/
theorem coneRelativeSpecTwistAlgebraIso_inv :
    (coneRelativeSpecTwistAlgebraIso 𝒜).inv =
      fromRelativeSpecOfAlgebraIso (pi 𝒜) (nonnegTwistAlgebraSheaf 𝒜)
        (coneAlgebraSheafIso 𝒜).symm :=
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
