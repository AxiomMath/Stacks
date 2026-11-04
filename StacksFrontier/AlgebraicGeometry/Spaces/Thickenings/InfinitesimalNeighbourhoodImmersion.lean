module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal neighbourhoods of an immersion of algebraic spaces

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S`. Stacks 05ZV constructs
its infinitesimal neighbourhoods as follows: choose an open subspace `U ⊆ X` in which `Z` is a
*closed* subspace, let `𝓘 ⊆ 𝒪_U` be the quasi-coherent sheaf of ideals cutting `Z` out of `U`,
and let `Z_n ⊆ U` be the closed subspace cut out by `𝓘 ^ (n + 1)`. The `n`th order
infinitesimal neighbourhood of `Z` in `X` is `Z_n`, and the first order one is `Z_1`.

Both halves of that construction are available in this tree. The open subspace is
`AlgebraicGeometry.Space.boundaryComplement` at the image of `i`, in which `i` is closed by
`AlgebraicGeometry.Space.exists_isClosedImmersion_comp_ι_boundaryComplement`; the sheaf of
ideals is `AlgebraicGeometry.Space.definingIdealSheaf`, and passing back from the power
`𝓘 ^ (n + 1)` to a closed subspace is the surjectivity half of Stacks 03MB,
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`.

## Main definitions

* `AlgebraicGeometry.Space.definingIdeals` is the defining ideal sheaf of a closed subspace,
  read as a sheaf of ideals on the small étale ringed site.
* `AlgebraicGeometry.Space.nthOrderNeighbourhood` is the closed subspace of an algebraic space
  `X` cut out by the `(n + 1)`st power of the defining ideal sheaf of a closed subspace `Z`.
* `AlgebraicGeometry.Space.immersionAmbientOpen` is the open subspace `U ⊆ X` of the source
  construction, read as an algebraic space, and
  `AlgebraicGeometry.Space.immersionSourceSubspace` is `Z` as a closed subspace of it.
* `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhoodOfImmersion` is **Stacks 05ZV**:
  the `n`th order infinitesimal neighbourhood `Z_n` of an immersion, and
  `AlgebraicGeometry.Space.firstOrderInfinitesimalNeighbourhoodOfImmersion` is the case
  `n = 1`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule_unit`: **a power of a
  quasi-coherent sheaf of ideals on an algebraic space is quasi-coherent**, which is what lets
  Stacks 03MB turn `𝓘 ^ (n + 1)` back into a closed subspace.
* `AlgebraicGeometry.Space.definingIdeals_nthOrderNeighbourhood`: the defining ideal sheaf of
  `Z_n` is `𝓘 ^ (n + 1)`, which characterises `Z_n` completely
  (`AlgebraicGeometry.Space.nthOrderNeighbourhood_unique`).
* `AlgebraicGeometry.Space.definingIdealAt_nthOrderNeighbourhood_of_isAffine`: on an affine
  étale chart the defining ideal of `Z_n` is the `(n + 1)`st power of that of `Z`.
* `AlgebraicGeometry.Space.le_nthOrderNeighbourhood` and
  `AlgebraicGeometry.Space.nthOrderNeighbourhood_mono`: `Z ⊆ Z_n`, and the neighbourhoods grow
  with their order.
* `AlgebraicGeometry.Space.le_nthOrderInfinitesimalNeighbourhoodOfImmersion` and
  `AlgebraicGeometry.Space.immersionClosedLift_comp_ι`: the inclusion `Z ⊆ Z_n` and the
  factorisation of `i` through `U`, which together make `Z ⊆ Z_n` a pair over `X`.
* `AlgebraicGeometry.Space.isNthOrderThickening_nthOrderNeighbourhood` and
  `AlgebraicGeometry.Space.isNthOrderThickening_nthOrderInfinitesimalNeighbourhoodOfImmersion`:
  **the order**, `AlgebraicGeometry.Space.IsNthOrderThickening` with ambient space `Z_n`, which
  is the remaining assertion of the definition — `Z ⊆ Z_n` is the *`n`th order* thickening of
  `Z` over `X`, and not merely some thickening.

## The order of the thickening

The subspace of `Z_n` whose order is measured is the image of `Z` under the inclusion
`Z ⟶ Z_n` coming from `AlgebraicGeometry.Space.le_nthOrderNeighbourhood`, that is, `Z` itself
read inside `Z_n`. It is the inverse image of `Z` along the closed immersion of `Z_n`
(`AlgebraicGeometry.Space.range_homOfLe_le_nthOrderNeighbourhood`), which is the spelling the
proof works in and the one the base change of a thickening, Stacks 09ZX, is stated in.

The order is read off the construction chart by chart. Every étale chart of `Z_n` is covered by
affine charts of `Z_n` fitting into affine chart diagrams over the ambient open `U`, by
Stacks 03G2 in the form
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`, and the vanishing of a power of a
defining ideal descends from a covering family,
`AlgebraicGeometry.Space.definingIdealAt_pow_eq_bot_of_ofArrows`. On such a chart the defining
ideal of `Z` is the extension of its defining ideal on the affine chart of `U` below it, by
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map`, so its `(n + 1)`st power is the
extension of `𝓘 ^ (n + 1)` there, which is the defining ideal of `Z_n`
(`AlgebraicGeometry.Space.definingIdealAt_nthOrderNeighbourhood_of_isAffine`) and is therefore
killed by pullback of regular functions to a chart of `Z_n`
(`AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`).

The topological half, that `Z ⊆ Z_n` is a thickening at all, comes from the point sets: the
point set of a closed subspace is the zero locus of its defining ideal sheaf
(`AlgebraicGeometry.Space.range_pointsMap_ι_eq_idealZeroLocus`), and an affine chart on which
`𝓘` is the unit ideal is one on which `𝓘 ^ (n + 1)` is the unit ideal, so `Z` already carries
every point of `Z_n`.

The same order read on a *scheme* chart, rather than at the ambient space `Z_n`, is
`Stacks.IdealSheaf.isNthOrderThickening_inclusion` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/InfinitesimalNeighbourhood.lean`.

## Implementation notes

The power `𝓘 ^ (n + 1)` is spelled `AlgebraicGeometry.Space.idealPowSubmodule`, the product of
the sheaf-of-ideals power with the structure sheaf read as a module over itself, because that
is the spelling in which quasi-coherence is available
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule`). It *is* the power of the
sheaf of ideals: `Stacks.Sites.idealSmul_top_unit` identifies `𝓘 · 𝒪_X` with `𝓘`, and
`AlgebraicGeometry.Space.idealPowSubmodule_unit_eq_idealPow` identifies `𝓘 ^ n 𝒪_X` with
`Stacks.Sites.idealPow`. Both rest on the scalar action on the structure sheaf read as a module
over itself being its own multiplication, and on the commutativity of the ring of sections,
which is recovered from `CommRingCat` where instance search sees only `RingCat`.

A closed subspace and its defining ideal sheaf are spelled over two different, definitionally
equal, descriptions of the small étale ringed site — `AlgebraicGeometry.Space.IdealSheaves`,
which the power machinery takes, and the submodule of
`AlgebraicGeometry.Space.structureRingSheaf` which
`AlgebraicGeometry.Space.definingIdealSheaf` produces. Instance search is syntactic, so the two
are bridged once, by `AlgebraicGeometry.Space.definingIdeals` and
`AlgebraicGeometry.Space.exists_definingIdeals_eq`, and everything after that stays on the
first spelling.

`Z_n` is obtained from `𝓘 ^ (n + 1)` by a choice, since Stacks 03MB is stated as an existence
statement; the choice is harmless because the closed subspace with a given defining ideal sheaf
is unique, which is `AlgebraicGeometry.Space.nthOrderNeighbourhood_unique`.

## References

* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 06EC](https://stacks.math.columbia.edu/tag/06EC)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace Stacks.Sites


variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}

/-- **`I · 𝒪 ⊆ I`.** A product of a section of a sheaf of ideals with a section of the structure
sheaf lies in the sheaf of ideals, because the scalar action on the structure sheaf read as a
module over itself is its own multiplication and the ring of sections is commutative. -/
theorem idealSmul_top_unit_le (I : IdealSubsheaf O) :
    idealSmul I
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule) ≤ I := by
  refine Stacks.SheafOfModules.sheafifySubmodule_le
    (presheafIdealSmul_le I fun X a ha m _ => ?_)
  have hcomm : ∀ b c : ((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X, b * c = c * b := by
    let : CommRing (((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X) :=
      CommRingCat.commRing (O.obj.obj X)
    exact fun b c => mul_comm b c
  have key : ∀ c : ((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X,
      a * c ∈
        (show Ideal (((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X) from I.obj X) := by
    intro c
    rw [hcomm]
    exact Ideal.mul_mem_left _ c ha
  exact key m

/-- **`I ⊆ I · 𝒪`.** A section of a sheaf of ideals is its own product with the unit section of
the structure sheaf. -/
theorem le_idealSmul_top_unit (I : IdealSubsheaf O) :
    I ≤ idealSmul I
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule) := by
  refine _root_.SheafOfModules.Submodule.le_iff.2 fun X a ha => ?_
  let : Semiring ((SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).val.obj X) :=
    inferInstanceAs (Semiring (((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X))
  have key : ∀ z : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).val.obj X,
      z = a →
      z ∈ (idealSmul I
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule)).obj X →
      a ∈ (idealSmul I
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule)).obj X :=
    fun _ hz hmem => hz ▸ hmem
  refine key
    (a • (1 : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).val.obj X)) ?_
    (smul_mem_idealSmul I ha (Stacks.SheafOfModules.mem_top_obj _))
  have h4 : ∀ b : ((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj X, b * 1 = b :=
    fun b => mul_one b
  exact h4 a

/-- **`I · 𝒪 = I`.** The product of a sheaf of ideals with the structure sheaf read as a module
over itself is the sheaf of ideals again. -/
theorem idealSmul_top_unit (I : IdealSubsheaf O) :
    idealSmul I
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule) = I :=
  le_antisymm (idealSmul_top_unit_le I) (le_idealSmul_top_unit I)

/-- **`I · R = I`** for an ideal of a commutative ring: the product of an ideal with the whole
ring read as a module over itself is the ideal. -/
theorem ideal_smul_top {R : Type*} [CommSemiring R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = I :=
  (Ideal.smul_eq_mul I ⊤).trans (Ideal.mul_top I)

/-- **`Iⁿ · 𝒪 = Iⁿ`.** The product of a power of a sheaf of ideals with the structure sheaf read
as a module over itself is that power. -/
theorem idealPowSmul_top_unit (I : IdealSubsheaf O) (n : ℕ) :
    idealPowSmul I n
        (⊤ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))).Submodule)
      = idealPow I n := by
  rw [idealPowSmul_eq_idealSmul, idealSmul_top_unit]

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A power of a quasi-coherent sheaf of ideals is quasi-coherent -/

section Power

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The structure sheaf of an algebraic space is quasi-coherent.** -/
theorem isQuasicoherentOnSite_unitModule :
    (unitModule B S hS hF).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit

/-- **A power of a quasi-coherent sheaf of ideals on an algebraic space is quasi-coherent.**
This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule` at the structure sheaf
read as a module over itself, where `𝓘 ^ n 𝒪_F` is the sheaf of ideals `𝓘 ^ n`. -/
theorem isQuasicoherentOnSite_idealPowSubmodule_unit (I : IdealSheaves B S hS F hF)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (n : ℕ) :
    (idealPowSubmodule I n (unitModule B S hS hF)).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_idealPowSubmodule B S hS F hF I (unitModule B S hS hF)
    (isQuasicoherentOnSite_unitModule B S hS F hF) hI n

/-- **`𝓘 ^ n 𝒪_F` is `𝓘 ^ n`.** The two spellings of the power of a sheaf of ideals — as the
product of `𝓘 ^ n` with the structure sheaf read as a module over itself, and as the sheaf of
ideals `Stacks.Sites.idealPow` — agree. -/
theorem idealPowSubmodule_unit_eq_idealPow (I : IdealSheaves B S hS F hF) (n : ℕ) :
    idealPowSubmodule I n (unitModule B S hS hF)
      = Stacks.Sites.idealPow (O := siteStructure B S hS F hF) I n :=
  Stacks.Sites.idealPowSmul_top_unit I n

/-- A positive power of a sheaf of ideals is contained in it. -/
theorem idealPowSubmodule_unit_succ_le_self (I : IdealSheaves B S hS F hF) (n : ℕ) :
    idealPowSubmodule I (n + 1) (unitModule B S hS hF) ≤ I := by
  refine le_trans (idealPowSubmodule_antitone I (unitModule B S hS hF)
    (Nat.succ_le_succ (Nat.zero_le n))) ?_
  rw [idealPowSubmodule_one]
  exact Stacks.Sites.idealSmul_top_unit_le I

end Power

/-! ### The neighbourhood cut out by a power of a defining ideal sheaf -/

section Neighbourhood

variable (X : AlgebraicSpaces B S hS)

/-- The defining ideal sheaf of a closed subspace, read as a sheaf of ideals on the small étale
ringed site of the ambient algebraic space. -/
def definingIdeals (Z : ClosedSubspaces B S hS X.1) : IdealSheaves B S hS X.1 X.2 :=
  definingIdealSheaf B S hS X Z

/-- The sections of the defining ideal sheaf over an étale chart are the defining ideal at that
chart. -/
theorem definingIdeals_obj (Z : ClosedSubspaces B S hS X.1)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    (definingIdeals B S hS X Z).obj V = definingIdealAt B S hS X Z V :=
  rfl

/-- The defining ideal sheaf of a closed subspace is quasi-coherent. -/
theorem isQuasicoherentOnSite_definingIdeals (Z : ClosedSubspaces B S hS X.1) :
    (definingIdeals B S hS X Z).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_definingIdealSheaf B S hS X Z

/-- **Stacks 03MB, surjectivity**, in the spelling of
`AlgebraicGeometry.Space.IdealSheaves`: every quasi-coherent sheaf of ideals of `𝒪_X` is the
defining ideal sheaf of a closed subspace of `X`. -/
theorem exists_definingIdeals_eq (N : IdealSheaves B S hS X.1 X.2)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    ∃ Z : ClosedSubspaces B S hS X.1, definingIdeals B S hS X Z = N := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X N hN
  exact ⟨Z, hZ⟩

/-- A closed subspace is contained in another if its defining ideal sheaf contains that of the
other. -/
private theorem le_of_definingIdeals_le (Z W : ClosedSubspaces B S hS X.1)
    (h : definingIdeals B S hS X W ≤ definingIdeals B S hS X Z) : Z.1 ≤ W.1 :=
  le_of_forall_definingIdealAt_le B S hS X Z W fun V _ =>
    _root_.SheafOfModules.Submodule.le_iff.1 h (op V)

/-- A closed subspace is determined by its defining ideal sheaf. -/
theorem eq_of_definingIdeals_eq (Z W : ClosedSubspaces B S hS X.1)
    (h : definingIdeals B S hS X Z = definingIdeals B S hS X W) : Z = W :=
  Subtype.ext (le_antisymm (le_of_definingIdeals_le B S hS X Z W h.ge)
    (le_of_definingIdeals_le B S hS X W Z h.le))

/-- **The `n`th order neighbourhood of a closed subspace.** The closed subspace of `X` whose
defining ideal sheaf is the `(n + 1)`st power of that of `Z`. It exists because that power is a
quasi-coherent sheaf of ideals, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule_unit`, and every
quasi-coherent sheaf of ideals is a defining ideal sheaf, by the surjectivity half of
Stacks 03MB. -/
@[ega "II 8.10.1" "more general",
  ega "IV 19.4.6" "more general",
  sga "2 XI 3.18" "more general",
  sga "7 IX 5.1" "more general"]
def nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    ClosedSubspaces B S hS X.1 :=
  (exists_definingIdeals_eq B S hS X
    (idealPowSubmodule (definingIdeals B S hS X Z) (n + 1) (unitModule B S hS X.2))
    (isQuasicoherentOnSite_idealPowSubmodule_unit B S hS X.1 X.2
      (definingIdeals B S hS X Z) (isQuasicoherentOnSite_definingIdeals B S hS X Z)
      (n + 1))).choose

/-- **The defining ideal sheaf of the `n`th order neighbourhood is `𝓘 ^ (n + 1)`.** This is the
defining property of the neighbourhood. -/
theorem definingIdeals_nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    definingIdeals B S hS X (nthOrderNeighbourhood B S hS X Z n) =
      idealPowSubmodule (definingIdeals B S hS X Z) (n + 1) (unitModule B S hS X.2) :=
  (exists_definingIdeals_eq B S hS X
    (idealPowSubmodule (definingIdeals B S hS X Z) (n + 1) (unitModule B S hS X.2))
    (isQuasicoherentOnSite_idealPowSubmodule_unit B S hS X.1 X.2
      (definingIdeals B S hS X Z) (isQuasicoherentOnSite_definingIdeals B S hS X Z)
      (n + 1))).choose_spec

/-- **The defining ideal sheaf of the `n`th order neighbourhood is the `(n + 1)`st power of
that of `Z`**, read as a power of sheaves of ideals. -/
theorem definingIdeals_nthOrderNeighbourhood_eq_idealPow (Z : ClosedSubspaces B S hS X.1)
    (n : ℕ) :
    definingIdeals B S hS X (nthOrderNeighbourhood B S hS X Z n) =
      Stacks.Sites.idealPow (O := siteStructure B S hS X.1 X.2)
        (definingIdeals B S hS X Z) (n + 1) :=
  (definingIdeals_nthOrderNeighbourhood B S hS X Z n).trans
    (idealPowSubmodule_unit_eq_idealPow B S hS X.1 X.2 (definingIdeals B S hS X Z) (n + 1))

/-- **The `n`th order neighbourhood is the unique closed subspace cut out by `𝓘 ^ (n + 1)`.**
The choice made in `AlgebraicGeometry.Space.nthOrderNeighbourhood` is therefore harmless. -/
theorem nthOrderNeighbourhood_unique (Z W : ClosedSubspaces B S hS X.1) (n : ℕ)
    (h : definingIdeals B S hS X W =
      idealPowSubmodule (definingIdeals B S hS X Z) (n + 1) (unitModule B S hS X.2)) :
    W = nthOrderNeighbourhood B S hS X Z n :=
  eq_of_definingIdeals_eq B S hS X W (nthOrderNeighbourhood B S hS X Z n)
    (h.trans (definingIdeals_nthOrderNeighbourhood B S hS X Z n).symm)

/-- **A closed subspace is contained in each of its neighbourhoods.** A positive power of a
sheaf of ideals is contained in it, and the correspondence of Stacks 03MB reverses
inclusions. -/
theorem le_nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    Z.1 ≤ (nthOrderNeighbourhood B S hS X Z n).1 := by
  refine le_of_definingIdeals_le B S hS X Z (nthOrderNeighbourhood B S hS X Z n) ?_
  rw [definingIdeals_nthOrderNeighbourhood]
  exact idealPowSubmodule_unit_succ_le_self B S hS X.1 X.2 (definingIdeals B S hS X Z) n

/-- The defining ideal sheaf of a closed subspace is cartesian on affine charts, read as a
sheaf of ideals on the small étale ringed site. -/
theorem isCartesianOnAffineCharts_definingIdeals (Z : ClosedSubspaces B S hS X.1) :
    IsCartesianOnAffineCharts (definingIdeals B S hS X Z).toSheafOfModules :=
  definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z

/-- **The defining ideal of the `n`th order neighbourhood on an affine étale chart is the
`(n + 1)`st power of the defining ideal of `Z` there.** This is the source's description of
`Z_n` as the closed subspace cut out by `𝓘 ^ (n + 1)`, read chart by chart; it is the form in
which the universal property of Stacks 05ZW reads the neighbourhood. -/
theorem definingIdealAt_nthOrderNeighbourhood_of_isAffine (Z : ClosedSubspaces B S hS X.1)
    (n : ℕ) (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V)) :
    definingIdealAt B S hS X (nthOrderNeighbourhood B S hS X Z n) (op V) =
      definingIdealAt B S hS X Z (op V) ^ (n + 1) := by
  have h1 : (definingIdeals B S hS X (nthOrderNeighbourhood B S hS X Z n)).obj (op V) =
      (idealPowSubmodule (definingIdeals B S hS X Z) (n + 1)
        (unitModule B S hS X.2)).obj (op V) :=
    congrArg (fun K : IdealSheaves B S hS X.1 X.2 => K.obj (op V))
      (definingIdeals_nthOrderNeighbourhood B S hS X Z n)
  have h2 := chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS X.1 X.2
    (definingIdeals B S hS X Z) (unitModule B S hS X.2) isCartesianOnAffineCharts_unit
    (isCartesianOnAffineCharts_definingIdeals B S hS X Z) (n + 1) hV
  have h3 := Stacks.Sites.ideal_smul_top
    (chartSectionIdeal B S hS X.1 X.2 (definingIdeals B S hS X Z) V ^ (n + 1))
  exact h1.trans (h2.trans h3)

/-- **The neighbourhoods of a closed subspace grow with their order.** A higher power of the
sheaf of ideals is smaller, so it cuts out a larger closed subspace. -/
theorem nthOrderNeighbourhood_mono (Z : ClosedSubspaces B S hS X.1) {m n : ℕ} (h : m ≤ n) :
    (nthOrderNeighbourhood B S hS X Z m).1 ≤ (nthOrderNeighbourhood B S hS X Z n).1 := by
  refine le_of_definingIdeals_le B S hS X (nthOrderNeighbourhood B S hS X Z m)
    (nthOrderNeighbourhood B S hS X Z n) ?_
  rw [definingIdeals_nthOrderNeighbourhood, definingIdeals_nthOrderNeighbourhood]
  exact idealPowSubmodule_antitone (definingIdeals B S hS X Z) (unitModule B S hS X.2)
    (Nat.succ_le_succ h)

/-! ### The order of the neighbourhood -/

/-- The extension of an ideal along a ring homomorphism has vanishing `m`th power as soon as the
`m`th power of the ideal is carried into the kernel. -/
private theorem map_pow_eq_bot_of_le_ker {R A : Type*} [CommSemiring R] [CommSemiring A]
    (φ : R →+* A) {I K : Ideal R} {m : ℕ} (hIK : I ^ m = K) (hK : K ≤ RingHom.ker φ) :
    Ideal.map φ I ^ m = ⊥ := by
  rw [← Ideal.map_pow, hIK]
  refine le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr ?_)
  rwa [← RingHom.ker_eq_comap_bot]

/-- The closed immersion of the `n`th order neighbourhood of a closed subspace into the ambient
algebraic space, read as a morphism of algebraic spaces over `S`. -/
abbrev nthOrderNeighbourhoodInclusion (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n) ⟶ X :=
  ObjectProperty.homMk (nthOrderNeighbourhood B S hS X Z n).1.ι

/-- **A chart on which the defining ideal of `Z` is the unit ideal is one on which the defining
ideal of its `n`th order neighbourhood is too.** On an affine chart the second ideal is the
`(n + 1)`st power of the first, and a power of the unit ideal is the unit ideal; the unit locus
is detected on affine charts. -/
theorem idealUnitLocus_definingIdealSheaf_subset_nthOrderNeighbourhood
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    idealUnitLocus B S hS X (definingIdealSheaf B S hS X Z) ⊆
      idealUnitLocus B S hS X
        (definingIdealSheaf B S hS X (nthOrderNeighbourhood B S hS X Z n)) := by
  intro x hx
  obtain ⟨V, hVaff, hVtop, hxV⟩ :=
    exists_affine_chart_obj_eq_top_of_mem_idealUnitLocus B S hS X
      (definingIdealSheaf B S hS X Z) hx
  have hV : IsAffine (chartScheme V) := hVaff
  refine (mem_idealUnitLocus_iff B S hS X _ x).2 ⟨V, ?_, hxV⟩
  show definingIdealAt B S hS X (nthOrderNeighbourhood B S hS X Z n) (op V) = ⊤
  rw [definingIdealAt_nthOrderNeighbourhood_of_isAffine B S hS X Z n V hV,
    show definingIdealAt B S hS X Z (op V) = ⊤ from hVtop]
  exact Ideal.top_pow _ _

/-- **A closed subspace carries every point of its `n`th order neighbourhood.** The point set of
a closed subspace is the zero locus of its defining ideal sheaf, and the unit locus of the
defining ideal of `Z` is contained in that of its neighbourhood. -/
theorem range_pointsMap_ι_nthOrderNeighbourhood_subset (Z : ClosedSubspaces B S hS X.1)
    (n : ℕ) :
    Set.range (pointsMap B S hS (nthOrderNeighbourhood B S hS X Z n).1.toFunctor
        (nthOrderNeighbourhood B S hS X Z n).1.ι) ⊆
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  rw [range_pointsMap_ι_eq_idealZeroLocus, range_pointsMap_ι_eq_idealZeroLocus]
  exact Set.compl_subset_compl.2
    (idealUnitLocus_definingIdealSheaf_subset_nthOrderNeighbourhood B S hS X Z n)

/-- **A closed subspace is a thickening of each of its neighbourhoods.** The inverse image of
`Z` along the inclusion of `Z_n` is a closed subspace of `Z_n`, and it is surjective on points
because `Z` already carries every point of `Z_n` and the inverse image is the fibre product. -/
theorem isThickening_preimage_nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    IsThickening B S hS
        (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
      (Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι) := by
  refine ⟨isClosedSubspace_preimage B S hS (nthOrderNeighbourhood B S hS X Z n).1.ι Z.1 X.2
    (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n)).2 Z.2, fun y => ?_⟩
  obtain ⟨z, hz⟩ := range_pointsMap_ι_nthOrderNeighbourhood_subset B S hS X Z n
    (Set.mem_range_self y)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (Subfunctor.isPullback_preimage (nthOrderNeighbourhood B S hS X Z n).1.ι Z.1) z y hz
  exact ⟨w, hw⟩

/-- **The defining ideal of `Z` inside its `n`th order neighbourhood has vanishing `(n + 1)`st
power on every étale chart of the neighbourhood.** Every chart of `Z_n` is covered by affine
charts fitting into affine chart diagrams over `X`, by Stacks 03G2, and the vanishing of a power
of a defining ideal descends from a covering family. On such a chart the defining ideal of the
inverse image of `Z` is the extension of the defining ideal of `Z` at the affine chart of `X`
below, so its `(n + 1)`st power is the extension of the defining ideal of `Z_n` there, and that
is killed by pullback of regular functions along a morphism factoring through `Z_n`. -/
theorem definingIdealAt_pow_succ_preimage_nthOrderNeighbourhood_eq_bot
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ)
    (U : SmallEtale B S hS
      (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n)).1) :
    definingIdealAt B S hS
        (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
        (⟨Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι,
          (isThickening_preimage_nthOrderNeighbourhood B S hS X Z n).1⟩ :
          ClosedSubspaces B S hS
            (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n)).1)
        (op U) ^ (n + 1) = ⊥ := by
  obtain ⟨J, W, a, d, hdU, hWaff, hVaff, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS
      (nthOrderNeighbourhoodInclusion B S hS X Z n) U
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS _ _ n U W a hcov fun i => ?_
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).V.1.left) := hVaff i
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).U.1.left) := by
    rw [hdU i]; exact hWaff i
  have hkey := definingIdealAt_preimage_eq_map B S hS
    (nthOrderNeighbourhoodInclusion B S hS X Z n) Z (d i).V (d i).U (d i).g (d i).comm.symm
  rw [← hdU i, show (⟨Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι,
        (isThickening_preimage_nthOrderNeighbourhood B S hS X Z n).1⟩ :
        ClosedSubspaces B S hS
          (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n)).1) =
      ⟨Z.1.preimage (nthOrderNeighbourhoodInclusion B S hS X Z n).hom,
        isClosedSubspace_preimage B S hS
          (nthOrderNeighbourhoodInclusion B S hS X Z n).hom Z.1 X.2
          (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n)).2 Z.2⟩ from rfl,
    hkey]
  have hle := definingIdealAt_le_ker_of_comp_eq B S hS X
    (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
    (nthOrderNeighbourhood B S hS X Z n)
    (nthOrderNeighbourhoodInclusion B S hS X Z n) (𝟙 _) (Category.id_comp _)
    (d i).V (d i).g (d i).U.1.hom (d i).comm.symm
  rw [Scheme.Γ_map_op] at hle
  exact map_pow_eq_bot_of_le_ker ((BigFppfOver.toScheme B S hS).map (d i).g).appTop.hom
    (definingIdealAt_nthOrderNeighbourhood_of_isAffine B S hS X Z n (d i).V hVa).symm hle

/-- **The inverse image of `Z` in its `n`th order neighbourhood is an `n`th order
thickening.** This is `AlgebraicGeometry.Space.isNthOrderThickening_nthOrderNeighbourhood` with
`Z` read inside `Z_n` as the inverse image `Z ×_X Z_n` of
`CategoryTheory.Subfunctor.preimage`, the spelling in which the base change of a thickening,
Stacks 09ZX, is stated. -/
theorem isNthOrderThickening_preimage_nthOrderNeighbourhood
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    IsNthOrderThickening B S hS n
        (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
      (Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι) :=
  ⟨isThickening_preimage_nthOrderNeighbourhood B S hS X Z n,
    definingIdealAt_pow_succ_preimage_nthOrderNeighbourhood_eq_bot B S hS X Z n⟩

/-- **`Z` read inside its `n`th order neighbourhood.** The image of `Z` under the inclusion
`Z ⟶ Z_n` furnished by `AlgebraicGeometry.Space.le_nthOrderNeighbourhood` is the inverse image
of `Z` along the closed immersion of `Z_n`: a section of `Z_n` comes from `Z` exactly when it
lies in `Z`. -/
theorem range_homOfLe_le_nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    Subfunctor.range (Subfunctor.homOfLe (le_nthOrderNeighbourhood B S hS X Z n)) =
      Z.1.preimage (nthOrderNeighbourhood B S hS X Z n).1.ι := by
  refine Subfunctor.ext (funext fun T => Set.ext fun x => ?_)
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

/-- **A closed subspace is an `n`th order thickening of its `n`th order neighbourhood.** This is
the order asserted by the definition of an infinitesimal neighbourhood, at the level of
algebraic spaces: the defining ideal of `Z`, read on the small étale site of `Z_n`, has
vanishing `(n + 1)`st power.

The subspace of `Z_n` is the image of `Z` under the inclusion `Z ⟶ Z_n` of
`AlgebraicGeometry.Space.le_nthOrderNeighbourhood`, that is, `Z` itself read inside `Z_n`. -/
theorem isNthOrderThickening_nthOrderNeighbourhood (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    IsNthOrderThickening B S hS n
        (closedSubspaceSpace B S hS X (nthOrderNeighbourhood B S hS X Z n))
      (Subfunctor.range (Subfunctor.homOfLe (le_nthOrderNeighbourhood B S hS X Z n))) := by
  rw [range_homOfLe_le_nthOrderNeighbourhood]
  exact isNthOrderThickening_preimage_nthOrderNeighbourhood B S hS X Z n

end Neighbourhood

/-! ### The infinitesimal neighbourhoods of an immersion -/

section Immersion

variable {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of an immersion is a locally closed set of points, so the complement of its
boundary is an open subspace. -/
theorem isOpenSubspace_immersionBoundaryComplement (hX : IsAlgebraicSpace B S hS X)
    (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    IsOpenSubspace B S hS
      (boundaryComplement B S hS X (Set.range (pointsMap B S hS Y i))) :=
  isOpenSubspace_boundaryComplement B S hS hX
    (isLocallyClosed_range_pointsMap_of_isImmersion B S hS hX i hi)

/-- **The open subspace in which an immersion is closed**, read as an algebraic space: the
complement of the boundary of the image of `i`, which is the open subspace `U ⊆ X` chosen by
Stacks 05ZV. -/
def immersionAmbientOpen (hX : IsAlgebraicSpace B S hS X) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) : AlgebraicSpaces B S hS :=
  ⟨(boundaryComplement B S hS X (Set.range (pointsMap B S hS Y i))).toFunctor,
    (isOpenSubspace_immersionBoundaryComplement B S hS hX i hi).1⟩

/-- The factorisation of an immersion through the complement of the boundary of its image. -/
def immersionClosedLift (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    Y ⟶ (immersionAmbientOpen B S hS hX i hi).1 :=
  (exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hY i hi).choose

/-- The factorisation of an immersion through the complement of the boundary of its image is a
closed immersion. -/
theorem isClosedImmersion_immersionClosedLift (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    IsClosedImmersion B S hS (immersionClosedLift B S hS hX hY i hi) :=
  (exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hY i hi).choose_spec.1

/-- The factorisation of an immersion through the complement of the boundary of its image
recovers the immersion. This is what puts the pair `Z ⊆ Z_n ⊆ U` of Stacks 05ZV *over `X`*: the
open subspace `U` sits in `X`, and `i` is the composite of the closed immersion of `Z` into `U`
with that inclusion. -/
@[stacks 05ZV "over `X`: the immersion is the closed immersion of `Z` into the open `U ⊆ X` \
followed by the inclusion of `U`, which is what puts `Z ⊆ Z_n` over `X`"]
theorem immersionClosedLift_comp_ι (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    immersionClosedLift B S hS hX hY i hi ≫
        (boundaryComplement B S hS X (Set.range (pointsMap B S hS Y i))).ι = i :=
  (exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hY i hi).choose_spec.2

/-- **The source of an immersion, as a closed subspace of the open subspace in which it is
closed.** This is the `Z ⊆ U` of Stacks 05ZV. -/
def immersionSourceSubspace (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    ClosedSubspaces B S hS (immersionAmbientOpen B S hS hX i hi).1 :=
  ⟨Subfunctor.range (immersionClosedLift B S hS hX hY i hi),
    isClosedSubspace_range_of_isClosedImmersion B S hS
      (immersionClosedLift B S hS hX hY i hi) hY
      (isClosedImmersion_immersionClosedLift B S hS hX hY i hi)⟩

/-- **Stacks 05ZV.** The *`n`th order infinitesimal neighbourhood* `Z_n` of an immersion
`i : Z ⟶ X` of algebraic spaces over `S`: the closed subspace of the open subspace `U ⊆ X` in
which `Z` is closed which is cut out by the `(n + 1)`st power of the quasi-coherent sheaf of
ideals of `Z` in `U`. -/
@[stacks 05ZV "the construction of `Z_n`: the closed subspace of the open `U = X ∖ ∂Z` cut out \
by `𝓘 ^ (n + 1)`", ega "II 8.10.1" "more general"]
def nthOrderInfinitesimalNeighbourhoodOfImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) (n : ℕ) :
    ClosedSubspaces B S hS (immersionAmbientOpen B S hS hX i hi).1 :=
  nthOrderNeighbourhood B S hS (immersionAmbientOpen B S hS hX i hi)
    (immersionSourceSubspace B S hS hX hY i hi) n

/-- **Stacks 05ZV, part (1).** The *first order infinitesimal neighbourhood* of an immersion:
the closed subspace cut out by the square of the sheaf of ideals of its source. -/
@[stacks 05ZV "part (1): the first order infinitesimal neighbourhood"]
abbrev firstOrderInfinitesimalNeighbourhoodOfImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) :
    ClosedSubspaces B S hS (immersionAmbientOpen B S hS hX i hi).1 :=
  nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi 1

/-- **The defining ideal sheaf of the `n`th order infinitesimal neighbourhood** is the
`(n + 1)`st power of the sheaf of ideals of the source. -/
theorem definingIdeals_nthOrderInfinitesimalNeighbourhoodOfImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) (n : ℕ) :
    definingIdeals B S hS (immersionAmbientOpen B S hS hX i hi)
        (nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi n) =
      Stacks.Sites.idealPow
        (O := siteStructure B S hS (immersionAmbientOpen B S hS hX i hi).1
          (immersionAmbientOpen B S hS hX i hi).2)
        (definingIdeals B S hS (immersionAmbientOpen B S hS hX i hi)
          (immersionSourceSubspace B S hS hX hY i hi)) (n + 1) :=
  definingIdeals_nthOrderNeighbourhood_eq_idealPow B S hS _ _ n

/-- **The source of an immersion is contained in each of its infinitesimal
neighbourhoods.** This is the inclusion `Z ⊆ Z_n` of Stacks 05ZV. -/
@[stacks 05ZV "the inclusion `Z ⊆ Z_n` inside the ambient open `U`"]
theorem le_nthOrderInfinitesimalNeighbourhoodOfImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) (n : ℕ) :
    (immersionSourceSubspace B S hS hX hY i hi).1 ≤
      (nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi n).1 :=
  le_nthOrderNeighbourhood B S hS _ _ n

/-- **Stacks 05ZV, the order.** The source of an immersion sits inside its `n`th order
infinitesimal neighbourhood as an `n`th order thickening: on the small étale site of `Z_n` the
`(n + 1)`st power of the defining ideal of `Z` vanishes. Together with
`AlgebraicGeometry.Space.le_nthOrderInfinitesimalNeighbourhoodOfImmersion` and
`AlgebraicGeometry.Space.immersionClosedLift_comp_ι` this is the assertion of the definition
that `Z ⊆ Z_n` is the *`n`th order* thickening of `Z` over `X`.

The subspace of `Z_n` is the image of `Z` under the inclusion `Z ⟶ Z_n` of
`AlgebraicGeometry.Space.le_nthOrderInfinitesimalNeighbourhoodOfImmersion`, that is, `Z` itself
read inside `Z_n`. -/
@[stacks 05ZV "the order: `Z ⊆ Z_n` is an nth order thickening, as the definition asserts"]
theorem isNthOrderThickening_nthOrderInfinitesimalNeighbourhoodOfImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) (n : ℕ) :
    IsNthOrderThickening B S hS n
        (closedSubspaceSpace B S hS (immersionAmbientOpen B S hS hX i hi)
          (nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi n))
      (Subfunctor.range (Subfunctor.homOfLe
        (le_nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi n))) :=
  isNthOrderThickening_nthOrderNeighbourhood B S hS _ _ n

/-- **Stacks 05ZV, part (1), the order.** The source of an immersion sits inside its first order
infinitesimal neighbourhood as a first order thickening. -/
theorem isFirstOrderThickening_firstOrderInfinitesimalNeighbourhoodOfImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) :
    IsFirstOrderThickening B S hS
        (closedSubspaceSpace B S hS (immersionAmbientOpen B S hS hX i hi)
          (firstOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi))
      (Subfunctor.range (Subfunctor.homOfLe
        (le_nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi 1))) :=
  isNthOrderThickening_nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi 1

/-- **The infinitesimal neighbourhoods of an immersion grow with their order.** -/
theorem nthOrderInfinitesimalNeighbourhoodOfImmersion_mono (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Y ⟶ X) (hi : IsImmersion B S hS i) {m n : ℕ}
    (h : m ≤ n) :
    (nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi m).1 ≤
      (nthOrderInfinitesimalNeighbourhoodOfImmersion B S hS hX hY i hi n).1 :=
  nthOrderNeighbourhood_mono B S hS _ _ h

end Immersion

end AlgebraicGeometry.Space

end
