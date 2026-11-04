module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedModule
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackAlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecData

/-!
# The algebra-sheaf hypotheses of the fibre instance of Tag 0897, discharged

`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`
runs part (2) of [Stacks, Tag 0897] on the graded algebra `g^*(j^*(⨁ₙ ℐⁿ))` of the square
```
Z --i--> X
|g       |f
v        v
Y --j--> S
```
and carries four hypotheses about that algebra as instance or explicit arguments, none of which
the library supplied: quasi-coherence of the two algebra sheaves `⨁ₙ j^*(ℐⁿ)` on `Y` and
`⨁ₙ g^*(j^*(ℐⁿ))` on `Z`, commutativity of the latter's homogeneous multiplication as a *class*,
quasi-coherence `hB` of its ungraded realization read as an `𝒪_Z`-module, and local
Noetherianness of its relative spectrum. This file discharges all of them.

Nothing here is new mathematics. The quasi-coherence statements are
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` at the two pullbacks, whose hypotheses
are already proved in
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedModule`
(`associatedGradedAlgebra_isQuasicoherent`, `associatedGradedAlgebra_negative_isZero`); `hB` is
the *definition* of quasi-coherence of an algebra sheaf, since
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of
`Stacks.RelativeSpec.gradedAlgebraSheaf` is the restriction of scalars of the unit along the
ungraded structure map; and local Noetherianness is
`Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` fed by the finite type of
`Stacks.GradedProperCohomology.isFiniteType_pullbackGradedAlgebraSheaf`, applied twice — once
along `j` to the Rees algebra sheaf of `ℐ`, which is of finite type as soon as `ℐ` is finitely
generated on affine opens (`Stacks.Blowup.isFiniteType_reesAlgebraSheaf`), and once along `g`.

## Main results

* `Stacks.AssociatedGradedFibre.isQuasicoherent_associatedGradedAlgebraSheaf` and
  `isQuasicoherent_fibreAssociatedGradedAlgebraSheaf`: **the two algebra sheaves are
  quasi-coherent**, as instances.
* `Stacks.AssociatedGradedFibre.isCommutative_gradedPullback_associatedGradedAlgebra`: **the
  class form of the commutativity**, as an instance.
* `Stacks.AssociatedGradedFibre.isQuasicoherent_ungradedRealization_fibreAssociatedGraded`:
  **`hB`.**
* `Stacks.AssociatedGradedFibre.isFiniteType_fibreAssociatedGradedAlgebraSheaf`:
  **`⨁ₙ g^*(j^*(ℐⁿ))` is an algebra sheaf of finite type** over an affine `S` and an affine `Y`,
  for `ℐ` finitely generated on affine opens, and
  `isLocallyNoetherian_relativeSpecOver_fibreAssociatedGraded` the local Noetherianness of its
  relative spectrum that follows over a locally Noetherian `Z`.

## Implementation notes

`S` and `Y` are required affine for the finite-type statements: the comparison of the two
pullbacks of a graded algebra sheaf is known locally surjective only over an affine base
(`Stacks.GradedComap.isLocallySurjective_unitPullbackHom`). At [Stacks, Tag 0D2N] `S = Spec A`
for a Noetherian local `A` and `Y = Spec κ(y)`, so neither is a restriction, and `ℐ = 𝔪` is
finitely generated because `A` is Noetherian — the variant
`isFiniteType_fibreAssociatedGradedAlgebraSheaf_of_isLocallyNoetherian` takes that form.

The commutativity instance is stated for the *class* `SheafOfModules.GradedAlgebra.IsCommutative`
and the quasi-coherence arguments for the *explicit* `hc` of
`Stacks.RelativeSpec.gradedAlgebraSheaf`; the two are the same statement by
`Stacks.GradedProperCohomology.isCommutative_of_heq`, and both are needed because an instance
argument cannot be used to build the algebra sheaf appearing in the surrounding types.

No `@[stacks]` attribute is attached: every statement is an instance of a tag already registered
in its own generality.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.GradedProperCohomology
open Stacks.Blowup
open Stacks.Conormal (gradedPullback)

universe u

namespace Stacks.AssociatedGradedFibre

/-! ### Quasi-coherence of the two algebra sheaves -/

section Quasicoherent

variable {Y S : Scheme.{u}} (j : Y ⟶ S) (I : S.IdealSheafData)

/-- The coproduct of the nonnegative pieces of `⨁ₙ j^*(ℐⁿ)` is quasi-coherent: the pieces are
(`Stacks.AssociatedGradedFibre.associatedGradedAlgebra_isQuasicoherent`), and a countable
coproduct of quasi-coherent modules is quasi-coherent after shrinking the index type
(`Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small`). -/
theorem isQuasicoherent_coprod_associatedGradedAlgebra :
    (∐ fun n : ℕ => (gradedPullback j (reesGradedAlgebra I)).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small
    (fun n : ℕ => (gradedPullback j (reesGradedAlgebra I)).piece (n : ℤ))
    fun n => associatedGradedAlgebra_isQuasicoherent j I (n : ℤ)

/-- **`⨁ₙ j^*(ℐⁿ)` is quasi-coherent as a sheaf of algebras on `Y`.** It is concentrated in
nonnegative degrees and the coproduct of its pieces is quasi-coherent, which is what
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` asks for. -/
instance isQuasicoherent_associatedGradedAlgebraSheaf :
    AlgebraSheaf.IsQuasicoherent
      (gradedAlgebraSheaf Y (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)) :=
  isQuasicoherent_gradedAlgebraSheaf Y (gradedPullback j (reesGradedAlgebra I)) _
    (associatedGradedAlgebra_negative_isZero j I)
    (isQuasicoherent_coprod_associatedGradedAlgebra j I)

variable {Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The pieces of `⨁ₙ g^*(j^*(ℐⁿ))` are quasi-coherent: one more pullback of a quasi-coherent
module. -/
theorem fibreAssociatedGradedAlgebra_isQuasicoherent (n : ℤ) :
    ((gradedPullback g (gradedPullback j (reesGradedAlgebra I))).piece n).IsQuasicoherent :=
  Stacks.Conormal.gradedPullback_isQuasicoherent g (gradedPullback j (reesGradedAlgebra I))
    (associatedGradedAlgebra_isQuasicoherent j I) n

/-- `⨁ₙ g^*(j^*(ℐⁿ))` is concentrated in nonnegative degrees. -/
theorem fibreAssociatedGradedAlgebra_negative_isZero (n : ℤ) (hn : n < 0) :
    IsZero ((gradedPullback g (gradedPullback j (reesGradedAlgebra I))).piece n) :=
  Stacks.Conormal.gradedPullback_negative_isZero g (gradedPullback j (reesGradedAlgebra I))
    (associatedGradedAlgebra_negative_isZero j I) n hn

/-- The coproduct of the nonnegative pieces of `⨁ₙ g^*(j^*(ℐⁿ))` is quasi-coherent. -/
theorem isQuasicoherent_coprod_fibreAssociatedGradedAlgebra :
    (∐ fun n : ℕ =>
      (gradedPullback g (gradedPullback j (reesGradedAlgebra I))).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.Cohomology.FormalFunctions.isQuasicoherent_coprod_of_small
    (fun n : ℕ => (gradedPullback g (gradedPullback j (reesGradedAlgebra I))).piece (n : ℤ))
    fun n => fibreAssociatedGradedAlgebra_isQuasicoherent j I g (n : ℤ)

/-- **`⨁ₙ g^*(j^*(ℐⁿ))` is quasi-coherent as a sheaf of algebras on `Z`**, which is the instance
argument `AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g …)` of the fibre instance of
part (2) of [Stacks, Tag 0897]. -/
instance isQuasicoherent_fibreAssociatedGradedAlgebraSheaf :
    AlgebraSheaf.IsQuasicoherent
      (pullbackGradedAlgebraSheaf g (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)) :=
  isQuasicoherent_gradedAlgebraSheaf Z
    (gradedPullback g (gradedPullback j (reesGradedAlgebra I))) _
    (fibreAssociatedGradedAlgebra_negative_isZero j I g)
    (isQuasicoherent_coprod_fibreAssociatedGradedAlgebra j I g)

/-- **The class form of the commutativity of the homogeneous multiplication of
`⨁ₙ g^*(j^*(ℐⁿ))`**, which `SheafOfModules.GradedModule.ungradedSheaf` resolves by instance
search. It is `Stacks.AssociatedGradedFibre.associatedGradedAlgebra_mul_comm` carried across one
more pullback and packaged by `Stacks.GradedProperCohomology.isCommutative_of_heq`. -/
instance isCommutative_gradedPullback_associatedGradedAlgebra :
    (gradedPullback g (gradedPullback j (reesGradedAlgebra I))).IsCommutative :=
  isCommutative_of_heq (gradedPullback g (gradedPullback j (reesGradedAlgebra I)))
    (Stacks.Conormal.gradedPullback_mul_comm g (gradedPullback j (reesGradedAlgebra I))
      (associatedGradedAlgebra_mul_comm j I))

/-- **`hB`: the ungraded realization of `⨁ₙ g^*(j^*(ℐⁿ))`, read as an `𝒪_Z`-module, is
quasi-coherent.**

This is quasi-coherence of the algebra sheaf itself written out:
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of
`Stacks.RelativeSpec.gradedAlgebraSheaf Z 𝓑 hc` is the restriction of scalars of the unit of
`SheafOfModules.GradedAlgebra.ungradedSheaf 𝓑` along `ungradedStructureMap`, because the sheaf
of rings of `gradedAlgebraSheaf` is that ungraded realization on the nose
(`Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf`) and its structure morphism is
`ungradedStructureMap`. -/
theorem isQuasicoherent_ungradedRealization_fibreAssociatedGraded :
    ((_root_.SheafOfModules.restrictScalars
        (gradedPullback g (gradedPullback j (reesGradedAlgebra I))).ungradedStructureMap).obj
      (_root_.SheafOfModules.unit
        (gradedPullback g
          (gradedPullback j (reesGradedAlgebra I))).ungradedSheaf)).IsQuasicoherent :=
  isQuasicoherent_fibreAssociatedGradedAlgebraSheaf j I g

end Quasicoherent

/-! ### Finite type and local Noetherianness of the relative spectrum -/

section FiniteType

variable {Y S : Scheme.{u}} (j : Y ⟶ S) (I : S.IdealSheafData)

/-- **`⨁ₙ j^*(ℐⁿ)` is an algebra sheaf of finite type on `Y`**, for an affine `S` over which `ℐ`
is finitely generated on affine opens.

`Stacks.GradedProperCohomology.isFiniteType_pullbackGradedAlgebraSheaf` along `j`, at the finite
type of the Rees algebra sheaf (`Stacks.Blowup.isFiniteType_reesAlgebraSheaf`). -/
theorem isFiniteType_associatedGradedAlgebraSheaf [IsAffine S]
    (hfg : ∀ U : S.affineOpens, (I.ideal U).FG) :
    AlgebraSheaf.IsFiniteType
      (gradedAlgebraSheaf Y (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)) :=
  isFiniteType_pullbackGradedAlgebraSheaf j (reesGradedAlgebra I) _
    (reesPiece_isQuasicoherent I) (isFiniteType_reesAlgebraSheaf I hfg)

variable {Z : Scheme.{u}} (g : Z ⟶ Y)

/-- **`⨁ₙ g^*(j^*(ℐⁿ))` is an algebra sheaf of finite type on `Z`**: the same statement one
pullback further along, with the affineness now that of `Y`. -/
theorem isFiniteType_fibreAssociatedGradedAlgebraSheaf [IsAffine S] [IsAffine Y]
    (hfg : ∀ U : S.affineOpens, (I.ideal U).FG) :
    AlgebraSheaf.IsFiniteType
      (pullbackGradedAlgebraSheaf g (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)) :=
  isFiniteType_pullbackGradedAlgebraSheaf g (gradedPullback j (reesGradedAlgebra I)) _
    (associatedGradedAlgebra_isQuasicoherent j I)
    (isFiniteType_associatedGradedAlgebraSheaf j I hfg)

/-- The same over a locally Noetherian `S`, where every ideal of sections is finitely
generated. -/
theorem isFiniteType_fibreAssociatedGradedAlgebraSheaf_of_isLocallyNoetherian [IsAffine S]
    [IsAffine Y] [IsLocallyNoetherian S] :
    AlgebraSheaf.IsFiniteType
      (pullbackGradedAlgebraSheaf g (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I)) :=
  isFiniteType_fibreAssociatedGradedAlgebraSheaf j I g fun U =>
    have := IsLocallyNoetherian.component_noetherian (X := S) U
    IsNoetherian.noetherian (I.ideal U)

/-- **`Spec_Z(⨁ₙ g^*(j^*(ℐⁿ))) ⟶ Z` has a locally Noetherian source**, which is the remaining
instance argument of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`.
This is [Stacks, Tag 01T6] through
`Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver`. -/
theorem isLocallyNoetherian_relativeSpecOver_fibreAssociatedGraded [IsAffine S] [IsAffine Y]
    [IsLocallyNoetherian Z] (hfg : ∀ U : S.affineOpens, (I.ideal U).FG) :
    IsLocallyNoetherian
      (relativeSpecOver (pullbackGradedAlgebraSheaf g (gradedPullback j (reesGradedAlgebra I))
        (associatedGradedAlgebra_mul_comm j I))).left :=
  isLocallyNoetherian_relativeSpecOver _
    (isFiniteType_fibreAssociatedGradedAlgebraSheaf j I g hfg)

end FiniteType

end Stacks.AssociatedGradedFibre

end
