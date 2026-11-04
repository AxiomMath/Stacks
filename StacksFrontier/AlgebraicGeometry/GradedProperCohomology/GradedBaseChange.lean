module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSectionsInt
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteTypeDominating.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.FiniteType

/-!
# The base change of [Stacks, Tag 0897], for an arbitrary sheaf of graded algebras

[Stacks, Tag 0897]'s proof replaces a graded `𝓑`-module `F` on `X` by a single module `F'` on
the relative spectrum `X' = Spec_X(𝓑)`. **This file performs that replacement for an arbitrary
sheaf of graded `𝒪_X`-algebras `𝓑`**, with no reference to where `𝓑` comes from: the input is
the datum `Stacks.AlgebraicGeometry.GradedProperCohomology.GradedQcohAlgebra`, which packages a
sheaf of graded algebras whose homogeneous multiplication is commutative, whose pieces are
quasi-coherent, and which vanishes in negative degrees.

Nothing here is about the grading *index set* beyond that: the total module is read as the
coproduct over all integer degrees, through
`SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf`, so no vanishing hypothesis on the
graded module itself is needed.

## Main definitions

* `GradedQcohAlgebra`: the datum above.
* `GradedQcohAlgebra.sheaf`: `𝓑` read as a sheaf of commutative `𝒪_X`-algebras, i.e. in the
  form a relative spectrum consumes ([Stacks, Tag 01LX]).
* `GradedQcohAlgebra.relSpec`: **`X' = Spec_X(𝓑)`**, as a scheme over `X`, with its affine
  structure morphism `π` and the identification `π_* 𝒪_{X'} ≅ 𝓑`
  (`GradedQcohAlgebra.relSpecIso`).
* `GradedQcohAlgebra.baseChangeModule`: **`F'`, the quasi-coherent `𝒪_{X'}`-module with
  `π_* F' ≅ ⨁ₙ Fₙ`** ([Stacks, Tag 01SB] at the relative spectrum), with
  `GradedQcohAlgebra.baseChangeModuleIso` the identification.

## Main results

* `GradedQcohAlgebra.isQuasicoherent_ungradedSheaf` and
  `GradedQcohAlgebra.isFiniteType_ungradedSheaf`: the total module is quasi-coherent over `𝓑`,
  and of finite type as soon as the graded module is.
* `GradedQcohAlgebra.isLocallyNoetherian_relSpec`: `X'` is locally Noetherian as soon as `X`
  is.
* `GradedQcohAlgebra.isCoherent_baseChangeModule`: **`F'` is coherent** when `X'` is locally
  Noetherian and `F` is quasi-coherent of finite type. Local Noetherianness of `X'` is available
  either from that of `X` together with finite type of the ungraded realization of `𝓑`
  (`isLocallyNoetherian_relSpec`), or — as in [Stacks, Tag 0897] itself — from a structure
  morphism `X' ⟶ Spec B` of finite type with `B` Noetherian.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

/-- **The datum out of which [Stacks, Tag 0897]'s base change is built**: a sheaf of graded
`𝒪_X`-algebras with commutative homogeneous multiplication, quasi-coherent pieces, vanishing in
negative degrees, and whose ungraded realization is an `𝒪_X`-algebra of finite type.

The commutativity is what `Stacks.RelativeSpec.gradedAlgebraSheaf` asks for before it will read
a sheaf of graded algebras as a sheaf of commutative algebras; the vanishing in negative degrees
and the quasi-coherence of the pieces are what make the ungraded realization quasi-coherent, so
that the relative spectrum can be formed.

Finite type of the ungraded realization is *not* a field: it is needed only for the local
Noetherianness of the relative spectrum and for the coherence of `F'`, and is an explicit
hypothesis there. -/
structure GradedQcohAlgebra (X : Scheme.{u}) where
  /-- The sheaf of graded algebras. -/
  alg : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf
  /-- Its homogeneous multiplication is commutative. -/
  isCommutative : alg.IsCommutative
  /-- It vanishes in negative degrees. -/
  isZero_of_neg : ∀ n : ℤ, n < 0 → IsZero (alg.piece n)
  /-- Its homogeneous pieces are quasi-coherent. -/
  isQuasicoherent_piece (n : ℤ) : (alg.piece n).IsQuasicoherent

namespace GradedQcohAlgebra

variable {X : Scheme.{u}} (D : GradedQcohAlgebra X)

attribute [instance] isCommutative isQuasicoherent_piece

/-- **`𝓑` as a sheaf of commutative `𝒪_X`-algebras**, i.e. in the form a relative spectrum
consumes. -/
abbrev sheaf : AlgebraSheaf X :=
  gradedAlgebraSheaf X D.alg fun i j W a b => D.isCommutative.mul_comm i j W a b

/-- The coproduct of the homogeneous pieces of `𝓑` is quasi-coherent. -/
theorem isQuasicoherent_coprod_piece :
    (∐ fun n : ℕ => D.alg.piece (n : ℤ)).IsQuasicoherent :=
  QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℕ => D.alg.piece (n : ℤ)) fun _ => D.isQuasicoherent_piece _

/-- **The ungraded realization of `𝓑` is quasi-coherent**, which is what the relative spectrum
consumes ([Stacks, Tag 01LX]). -/
instance isQuasicoherent_sheaf : AlgebraSheaf.IsQuasicoherent D.sheaf :=
  isQuasicoherent_gradedAlgebraSheaf X D.alg _ D.isZero_of_neg
    D.isQuasicoherent_coprod_piece

/-- **`X' = Spec_X(𝓑)`**, the relative spectrum, as a scheme over `X`. This is the base change
of [Stacks, Tag 0897]'s proof, built by [Stacks, Tag 01LX]. -/
abbrev relSpec : Over X := FiniteTypeDominating.relativeSpecOver D.sheaf

/-! ### The total module of a graded module -/

variable (M : _root_.SheafOfModules.GradedModule.{u, u, u} D.alg)

/-- The coproduct of the homogeneous pieces of a graded module with quasi-coherent pieces is
quasi-coherent. -/
theorem isQuasicoherent_coprod_pieceModule
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent) :
    (∐ fun n : ℤ => M.piece n).IsQuasicoherent :=
  QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℤ => M.piece n) fun _ => hqc _

/-- **The total module `⨁ₙ Fₙ` of a graded `𝓑`-module is quasi-coherent over `𝓑`** as soon as
its homogeneous pieces are quasi-coherent.

The `𝒪_X`-module underlying it is the coproduct `∐_{n : ℤ} Fₙ`
(`coprodIntIsoUngradedSheaf`), and that coproduct is quasi-coherent; quasi-coherence then passes
to the module over `𝓑` by [Stacks, Tag 0H88]. -/
theorem isQuasicoherent_ungradedSheaf (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent) :
    (_root_.SheafOfModules.GradedModule.ungradedSheaf M).IsQuasicoherent := by
  have hres : ((_root_.SheafOfModules.restrictScalars D.alg.ungradedStructureMap).obj
      (_root_.SheafOfModules.GradedModule.ungradedSheaf M)).IsQuasicoherent :=
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      M.coprodIntIsoUngradedSheaf (D.isQuasicoherent_coprod_pieceModule M hqc)
  exact Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    D.alg.ungradedStructureMap D.isQuasicoherent_sheaf
    (_root_.SheafOfModules.GradedModule.ungradedSheaf M) hres

/-- **The total module is of finite type over `𝓑`** as soon as the graded module is, which is
[Stacks, Tag 0897]'s own hypothesis on it. -/
theorem isFiniteType_ungradedSheaf (hft : M.IsFiniteType) :
    (_root_.SheafOfModules.GradedModule.ungradedSheaf M).IsFiniteType :=
  _root_.SheafOfModules.GradedModule.isFiniteType_ungradedSheaf M hft

/-! ### `F'` on `X'` -/

variable (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)

/-- The total module, packaged as a quasi-coherent module over the ungraded realization of `𝓑`,
i.e. in the form [Stacks, Tag 01SB] consumes. -/
def totalQcoh :
    (_root_.SheafOfModules.isQuasicoherent (AlgebraSheaf.ringSheaf D.sheaf)).FullSubcategory :=
  ⟨_root_.SheafOfModules.GradedModule.ungradedSheaf M, D.isQuasicoherent_ungradedSheaf M hqc⟩

/-- **`F'`: the quasi-coherent `𝒪_{X'}`-module on `X' = Spec_X(𝓑)` whose direct image is the
total module `⨁ₙ Fₙ`.** This is [Stacks, Tag 01SB] at the relative spectrum, applied to the
total module. -/
def baseChangeModule : D.relSpec.left.Modules :=
  ((relativeSpecQcohEquivalence D.sheaf).inverse.obj (D.totalQcoh M hqc)).obj

/-- `F'` is quasi-coherent. -/
instance isQuasicoherent_baseChangeModule : (D.baseChangeModule M hqc).IsQuasicoherent :=
  ((relativeSpecQcohEquivalence D.sheaf).inverse.obj (D.totalQcoh M hqc)).property

/-- **`π_* F' ≅ ⨁ₙ Fₙ`**: the defining property of `F'`. -/
def baseChangeModuleIso :
    (relativeSpecQcohEquivalence D.sheaf).functor.obj
        ((relativeSpecQcohEquivalence D.sheaf).inverse.obj (D.totalQcoh M hqc)) ≅
      D.totalQcoh M hqc :=
  (relativeSpecQcohEquivalence D.sheaf).counitIso.app (D.totalQcoh M hqc)

/-- **`F'` is of finite type** as soon as the graded module is: the total module is of finite
type over `𝓑 = π_* 𝒪_{X'}`, and finite type transports across [Stacks, Tag 01SB]. -/
theorem isFiniteType_baseChangeModule (hft : M.IsFiniteType) :
    (D.baseChangeModule M hqc).IsFiniteType :=
  isFiniteType_inverse_obj D.sheaf (D.totalQcoh M hqc) (D.isFiniteType_ungradedSheaf M hft)

/-- **`F'` is coherent** when `X'` is locally Noetherian and the graded module is quasi-coherent
of finite type. This is [Stacks, Tag 01XZ] on `X'`. -/
theorem isCoherent_baseChangeModule (hXN : IsLocallyNoetherian D.relSpec.left)
    (hft : M.IsFiniteType) : (D.baseChangeModule M hqc).IsCoherent :=
  have := hXN
  have := D.isFiniteType_baseChangeModule M hqc hft
  CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType (D.baseChangeModule M hqc)

end GradedQcohAlgebra

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
