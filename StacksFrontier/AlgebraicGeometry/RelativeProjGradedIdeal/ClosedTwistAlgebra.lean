module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.GeneratedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists of a relative Proj along a closed subscheme, and Tag 0801's homomorphism

Tag 0801 takes the kernel of a homomorphism of graded `𝒪_S`-algebras
`ψ : 𝒜 ⟶ ⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))`, for `i : Z ⟶ Proj_S(𝒜)` a closed subscheme and `p` the
structure morphism. `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistHom.lean` built
the homogeneous-section map `𝒜 ⟶ ⨁_{d ≥ 0} p_*(𝒪(d))` as a single homomorphism; **what this file
supplies is the graded algebra `d ↦ (i_*𝒪_Z)(d)` on `Proj_S(𝒜)` together with its quotient
homomorphism `q`**, and then `ψ`, its graded ideal, its quotient and the closed immersion
`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`.

## Main definitions

* `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.ofSheafGradedAlgebra`: the conversion from the
  data of Situation 01NN back to a sheaf of graded algebras in the sense of Tag 0FQW.
* `Stacks.AlgebraicGeometry.NonnegTruncation.pushforwardNonnegHom`: **the truncated direct image
  of a nonnegative multiplicative family of morphisms**, `(p_*B)_{≥0} ⟶ (p_*C)_{≥0}`.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.twistSheafGradedAlgebra`: **the twists of a
  relative Proj as data of Situation 01NN on `Proj_S(𝒜)`**, i.e. truncated to the nonnegative
  degrees.
* `…RelativeProjTwists.restrictionToClosed`: the restriction `M ⟶ i_*i^*M` of a module on
  `Proj_S(𝒜)` to a closed subscheme, the unit of `i^* ⊣ i_*`.
* `…RelativeProjTwists.closedIdealDegreeZero`: **the ideal sheaf `ℐ_Z` of the closed subscheme,
  as a submodule of the degree-zero twist** — the local sections of `𝒪(0)` restricting to zero
  on `Z`.
* `…RelativeProjTwists.closedGradedIdeal`: the graded ideal of the twists generated in degree `0`
  by a submodule of the degree-zero twist — for `ℐ_Z`, the graded ideal `d ↦ ℐ_Z · 𝒪(d)`.
* `…RelativeProjTwists.restrictedTwistAlgebra` and `…restrictionHom`: **the graded algebra
  `d ↦ (i_*𝒪_Z)(d)` and its quotient homomorphism `q`.**
* `…RelativeProjTwists.closedTwistTarget`: the target `⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))` of Tag 0801's
  homomorphism.
* `…RelativeProjTwists.psiClosedHom`: **Tag 0801's `ψ`**, the homogeneous-section map composed
  with the truncated direct image of `q`.
* `…RelativeProjTwists.closedVanishingIdeal`: **Tag 0801's graded ideal `ℐ`**, the degreewise
  kernel of `ψ`.
* `…RelativeProjTwists.closedQuotient`, `…closedQuotientMk` and `…closedAmbientHom`: the quotient
  `𝒜/ℐ`, the quotient homomorphism and `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`.

## Main results

* `…RelativeProjTwists.quasiSeparated_toBase` and `…isQuasicoherent_pushforward_twist`: **the
  quasi-coherence hypothesis `hqc` of `…RelativeProjTwists.psiHom` is discharged** from
  quasi-compactness of the structure morphism alone, which is Tag 0801's own hypothesis. This is
  Tag 01LC applied to a quasi-compact quasi-separated morphism, separatedness being
  `…RelativeProjSeparated.isSeparated_toBase`.
* `…isQuasicoherent_pushforward_piece`: the same for the direct image of any homogeneous piece of
  any data of Situation 01NN on `Proj_S(𝒜)`, which discharges the quasi-coherence hypothesis of
  `closedTwistTarget`.
* `…RelativeProjTwists.epi_restrictionToClosed`: the restriction to a closed subscheme is
  surjective, and `…isQuasicoherent_pushforward_pullback`: `i_*i^*M` is quasi-coherent when `M`
  is — `i^*` preserves quasi-coherence and `i` is affine.
* `…RelativeProjTwists.mem_closedIdealDegreeZero_iff` and
  `…isQuasicoherent_closedIdealDegreeZero`: `ℐ_Z` is cut out by vanishing on `Z` and is
  quasi-coherent, being a sectionwise kernel of a morphism of quasi-coherent modules.
* `…RelativeProjTwists.restrictionHom_app_eq_zero_iff`: a homogeneous local section of the twists
  dies in `(i_*𝒪_Z)(n)` exactly when it lies in `ℐ_Z · 𝒪(n)`.
* `…RelativeProjTwists.mem_closedVanishingIdeal_iff` and `…closedQuotientMk_app_eq_zero_iff`:
  **Tag 0801's kernel clause** for `ψ`.
* `…RelativeProjTwists.surjectiveOnAffineSections_closedQuotientMk` and
  `…isClosedImmersion_closedAmbientHom`: `Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.

## Implementation notes

**The quotient is taken at the level of Situation 01NN, not below it.** The twists live on
`Proj_S(𝒜)` and are *not* concentrated in nonnegative degrees — `𝒪(-1)` is not a zero object — so
at first sight the graded-ideal and quotient machinery of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Basic.lean` and `…/Quotient.lean`, which
is typed over `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, does not reach
them, and the quotient would have to be redone one level down, for a
`SheafOfModules.GradedAlgebra`. **It does not have to be.** Truncating the twists *first* costs
one line — `Stacks.AlgebraicGeometry.NonnegTruncation.nonnegSheafGradedAlgebra` applied to
`TwistData.algebra`, with `TwistData.mul_comm` and `TwistData.isQuasicoherent` as its two
arguments — and nothing is lost, because the direct sum of Tag 0801 runs over the nonnegative
degrees only. After that the twists *are* data of Situation 01NN on `Proj_S(𝒜)` and the existing
graded-ideal and quotient machinery applies verbatim, with no duplication one level down.

**Where the `ℕ`-indexed family comes in.** `pushforwardNonnegHom` takes its data as a family
indexed by `ℕ` rather than by `ℤ`, because the source and the target of the quotient homomorphism
`q` agree with the untruncated twists only in the nonnegative degrees. The negative components
are forced: both sides are zero objects there, so the component is the zero morphism and both
laws compare two zeros. The case split is on the constructors of `ℤ`, so that `(↑i + ↑j)` reduces
to `↑(i + j)` and the nonnegative branch of each law is *literally* the law of `q`, with no
transport — the same observation the truncation itself rests on.

**One piece of general machinery is introduced here** rather than in the file that owns the
notion, to avoid rebuilding that tree: `SheafSymmetricAlgebra.ofSheafGradedAlgebra`, the
conversion inverse to `…SheafSymmetricAlgebra.toSheafGradedAlgebra`, which
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Bridge.lean` does not have — its "Not done
here" records only that `SheafOfModules.GradedAlgebra.Hom` is not carried across. It is pure
repackaging. Composition of homomorphisms of sheaf-level graded algebras is *not* introduced
here: `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.comp` already exists,
in `StacksFrontier/AlgebraicGeometry/Morphism/Composition.lean`, in the
`(outer).comp (inner)` argument order, and that is what `psiClosedHom` uses. The "Not done here"
of `StacksFrontier/AlgebraicGeometry/RelativeProjMapDomain/Hom.lean`, which says that "nothing is
proved about morphisms" because "`SheafGradedAlgebra` has no morphisms", is about that file and
should not be read as saying the composite does not exist.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)

## Not done here

No Stacks tag is claimed here. **Tag 0801's relative `iso` clause is proved**, downstream, in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`: the
chart-level hypothesis the reductions of this file leave is discharged there by
`Stacks.AlgebraicGeometry.RelativeProjTwists.ker_eq_chartMap_ker`, and the whole of
`…RelativeProjGradedIdeal.VanishingIdealPresentation` is built as
`…RelativeProjTwists.vanishingIdealPresentation`, on no hypothesis beyond Tag 0801's own. Tag
0803 is registered with that presentation discharged in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

What closed the clause, on top of the reductions here: the chart comparison
`…RelativeProjTwists.pullbackGlobalSections_degreeSection_eq_zero_iff`, which composes
`…RelativeProjTwists.TwistData.ψ_chart` with the base change of the unit `M ⟶ i_*i^*M` along an
arbitrary open immersion (`Stacks.AlgebraicGeometry.ChartUnit.app_unit_eq_zero_iff`) and with
`…RelativeProjTwists.restrictionHom_app_eq_zero_iff_restrictionToClosed`; the resulting equality
of homogeneous ideals `…RelativeProjTwists.sectionGradedIdeal_eq_idealOfClosedSubscheme`; and the
absolute case of Tag 0801 restated at an `AddSubgroup`-valued grading,
`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.PushforwardGradedAlgebra
open Stacks.AlgebraicGeometry.NonnegTruncation
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped ZeroObject

universe u

/-! ### Reading data of Situation 01NN as a sheaf of graded algebras -/

namespace Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- **The conversion back.** Sheaf-level graded algebra data of Situation 01NN is in particular a
sheaf of graded algebras in the sense of Tag 0FQW: commutativity, nonnegativity and
quasi-coherence are forgotten, and the restriction-compatible family of units becomes a global
section of the degree-zero piece. -/
def ofSheafGradedAlgebra (B : SheafGradedAlgebra S) :
    SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf where
  piece := B.piece
  mul i j :=
    { app W := (B.mul i j).app W.unop
      map_smul_left W r x y := (B.mul i j).map_smul_left W.unop r x y
      map_smul_right W r x y := (B.mul i j).map_smul_right W.unop r x y
      naturality f x y := (B.mul i j).naturality (leOfHom f.unop) x y }
  one := PresheafOfModules.sectionsMk (fun W => B.one W.unop)
    fun {_ _} f => B.one_res (leOfHom f.unop)
  mul_assoc i j k W := B.mul_assoc i j k W.unop
  one_mul i W := B.one_mul i W.unop
  mul_one i W := B.mul_one i W.unop

/-- The graded pieces of `ofSheafGradedAlgebra B` are the graded pieces of `B`. -/
@[simp] theorem ofSheafGradedAlgebra_piece (B : SheafGradedAlgebra S) (n : ℤ) :
    (ofSheafGradedAlgebra B).piece n = B.piece n := rfl

/-- On an open `U`, the multiplication of `ofSheafGradedAlgebra B` is the multiplication of `B`. -/
theorem ofSheafGradedAlgebra_mul_app (B : SheafGradedAlgebra S) (i j : ℤ) (U : S.Opens) :
    ((ofSheafGradedAlgebra B).mul i j).app (op U) = (B.mul i j).app U := rfl

/-- The unit of `ofSheafGradedAlgebra B`, evaluated on an open `U`, is `B.one U`. -/
theorem ofSheafGradedAlgebra_one_eval (B : SheafGradedAlgebra S) (U : S.Opens) :
    (ofSheafGradedAlgebra B).one.eval (op U) = B.one U := rfl

/-- Commutativity survives the conversion back. -/
theorem isCommutative_ofSheafGradedAlgebra (B : SheafGradedAlgebra S) :
    IsCommutative (ofSheafGradedAlgebra B) :=
  fun i j U a b => B.mul_comm i j U.unop a b

end Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

/-! ### The truncated direct image of a homomorphism -/

namespace Stacks.AlgebraicGeometry.NonnegTruncation

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X S : Scheme.{u}} (p : X ⟶ S)
  (B C : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hcB : IsCommutative B)
  (hqB : ∀ n : ℤ, (((Scheme.Modules.pushforward p).obj (B.piece n) : S.Modules)).IsQuasicoherent)
  (hcC : IsCommutative C)
  (hqC : ∀ n : ℤ, (((Scheme.Modules.pushforward p).obj (C.piece n) : S.Modules)).IsQuasicoherent)
  (φ : ∀ n : ℕ, B.piece (n : ℤ) ⟶ C.piece (n : ℤ))

/-- The degree-`n` component of the truncated direct image of a nonnegative family of morphisms:
the direct image of the `n`-th member in a nonnegative degree, and the zero morphism between two
zero objects in a negative one. -/
def pushNonnegHomApp : ∀ n : ℤ,
    (pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece n ⟶
      (pushforwardNonnegSheafGradedAlgebra p C hcC hqC).piece n
  | .ofNat n => (Scheme.Modules.pushforward p).map (φ n)
  | .negSucc _ => 0

/-- In a nonnegative degree `n`, the component of `pushNonnegHomApp` on an open `U` is the
component of `φ n` on the preimage `p ⁻¹ᵁ U`. -/
theorem pushNonnegHomApp_app_ofNat (n : ℕ) (U : S.Opens)
    (a : Γ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece (.ofNat n), U)) :
    (pushNonnegHomApp p B C hcB hqB hcC hqC φ (.ofNat n)).app U a =
      (φ n).val.app (op (p ⁻¹ᵁ U)) a := rfl

/-- A product of local sections of `(p_*B)_{≥0}` in which the left degree is negative vanishes. -/
private theorem push_zero_left (a : ℕ) (j : ℤ) (U : S.Opens)
    (x : Γ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece (.negSucc a), U))
    (y : Γ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece j, U)) :
    ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).mul (.negSucc a) j).app U x y = 0 :=
  mul_app_apply_eq_zero_of_neg_left (pushforwardGradedAlgebra p B) a j (op U) x y

/-- A product of local sections of `(p_*B)_{≥0}` in which the right degree is negative
vanishes. -/
private theorem push_zero_right (i : ℤ) (b : ℕ) (U : S.Opens)
    (x : Γ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece i, U))
    (y : Γ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).piece (.negSucc b), U)) :
    ((pushforwardNonnegSheafGradedAlgebra p B hcB hqB).mul i (.negSucc b)).app U x y = 0 :=
  mul_app_apply_eq_zero_of_neg_right (pushforwardGradedAlgebra p B) i b (op U) x y

/-- **The truncated direct image of a nonnegative multiplicative family of morphisms**, as a
homomorphism of sheaf-level graded algebras `(p_*B)_{≥0} ⟶ (p_*C)_{≥0}`.

Only the nonnegative degrees carry data: in a negative degree both sides are zero objects, so
the component is the zero morphism and both the product and the unit law are comparisons of two
zeros. -/
def pushforwardNonnegHom
    (hmul : ∀ (i j : ℕ) (W : X.Opens) (a : (B.piece (i : ℤ)).val.obj (op W))
        (b : (B.piece (j : ℤ)).val.obj (op W)),
      (φ (i + j)).val.app (op W) ((B.mul (i : ℤ) (j : ℤ)).app (op W) a b) =
        (C.mul (i : ℤ) (j : ℤ)).app (op W) ((φ i).val.app (op W) a) ((φ j).val.app (op W) b))
    (hone : ∀ W : X.Opens, (φ 0).val.app (op W) (B.one.eval (op W)) = C.one.eval (op W)) :
    SheafGradedAlgebraHom (pushforwardNonnegSheafGradedAlgebra p B hcB hqB)
      (pushforwardNonnegSheafGradedAlgebra p C hcC hqC) where
  app := pushNonnegHomApp p B C hcB hqB hcC hqC φ
  app_mul i j U a b := by
    rcases i with m | m
    · rcases j with n | n
      · exact hmul m n (p ⁻¹ᵁ U) a b
      · rw [push_zero_right p B hcB hqB _ n U a b, map_zero]
        exact (push_zero_right p C hcC hqC _ n U _ _).symm
    · rw [push_zero_left p B hcB hqB m j U a b, map_zero]
      exact (push_zero_left p C hcC hqC m j U _ _).symm
  app_one U := hone (p ⁻¹ᵁ U)

end Stacks.AlgebraicGeometry.NonnegTruncation

/-! ### The twists of a relative Proj as data of Situation 01NN -/

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (D : TwistData A)

/-- **The twists of a relative Proj, truncated to the nonnegative degrees, as sheaf-level graded
algebra data on `Proj_S(𝒜)`** in the sense of Situation 01NN.

The twists are quasi-coherent and commutative outright; the one thing Situation 01NN asks of them
that they do not have is that the negative pieces be zero objects, and the truncation supplies
exactly that. Nothing is lost: the direct sum of Tag 0801 runs over the nonnegative degrees. -/
def twistSheafGradedAlgebra : SheafGradedAlgebra (relativeProj A).scheme :=
  nonnegSheafGradedAlgebra D.algebra D.mul_comm D.isQuasicoherent

/-- In a nonnegative degree the data is the twist itself, on the nose. -/
theorem twistSheafGradedAlgebra_piece_ofNat (n : ℕ) :
    (twistSheafGradedAlgebra D).piece (.ofNat n) = D.algebra.piece (.ofNat n) := rfl

/-! ### Quasi-coherence of the direct images, from quasi-compactness alone -/

/-- **The structure morphism of a relative Proj is quasi-separated**: it is separated. -/
instance quasiSeparated_toBase : QuasiSeparated (relativeProj A).toBase :=
  have : IsSeparated (relativeProj A).toBase :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase A (relativeProj A)
  inferInstance

/-- **The direct images of the twists are quasi-coherent**, with quasi-compactness of the
structure morphism as the only hypothesis — which is Tag 0801's own hypothesis.

This is Tag 01LC for the quasi-compact quasi-separated `p`: quasi-compactness is assumed,
separatedness is `…RelativeProjSeparated.isSeparated_toBase`, and the twists are quasi-coherent
outright. It discharges the `hqc` argument of
`Stacks.AlgebraicGeometry.RelativeProjTwists.psiHom`. -/
@[ega "II 3.3.4" "special case"]
theorem isQuasicoherent_pushforward_twist [QuasiCompact (relativeProj A).toBase] (n : ℤ) :
    (((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (D.algebra.piece n) : S.Modules)).IsQuasicoherent :=
  have := D.isQuasicoherent n
  AlgebraicGeometry.pushforward_isQuasicoherent _ _

/-- **The direct images of the homogeneous pieces of any data of Situation 01NN on `Proj_S(𝒜)`
are quasi-coherent**, again from quasi-compactness alone. This discharges the quasi-coherence
hypothesis of the target of Tag 0801's homomorphism. -/
theorem isQuasicoherent_pushforward_piece [QuasiCompact (relativeProj A).toBase]
    (B : SheafGradedAlgebra (relativeProj A).scheme) (n : ℤ) :
    (((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (B.piece n) : S.Modules)).IsQuasicoherent :=
  AlgebraicGeometry.pushforward_isQuasicoherent _ _

/-! ### The ideal sheaf of a closed subscheme, in the degree-zero twist -/

section ClosedSubscheme

variable {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme)

/-- **The restriction of a module on `Proj_S(𝒜)` to a closed subscheme**, `M ⟶ i_*i^*M`: the unit
of the adjunction `i^* ⊣ i_*`. For `M` the structure sheaf this is `𝒪 ⟶ i_*𝒪_Z`, and for `M` the
degree-`d` twist it is `𝒪(d) ⟶ (i_*𝒪_Z)(d)`. -/
abbrev restrictionToClosed (M : (relativeProj A).scheme.Modules) :
    M ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M

/-- **The restriction to a closed subscheme is surjective**, by
`Stacks.ClosedImmersion.epi_unit_app`. -/
theorem epi_restrictionToClosed [IsClosedImmersion i] (M : (relativeProj A).scheme.Modules) :
    Epi (restrictionToClosed i M) :=
  Stacks.ClosedImmersion.epi_unit_app i M

/-- **The restriction of a quasi-coherent module to a closed subscheme, pushed back forward, is
quasi-coherent**: `i^*` preserves quasi-coherence (Tag 01BG) and `i` is an affine morphism, so
`i_*` does too (Tag 02KG). -/
theorem isQuasicoherent_pushforward_pullback [IsClosedImmersion i]
    (M : (relativeProj A).scheme.Modules) [M.IsQuasicoherent] :
    (((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M) :
      (relativeProj A).scheme.Modules)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom i _

/-- **The ideal sheaf of the closed subscheme, as a submodule of the degree-zero twist**: the
local sections of `𝒪(0)` that restrict to zero on `Z`.

This is the `ℐ_Z` that Tag 0801's graded ideal is generated by in degree `0`. It is a submodule
of the degree-zero *twist* rather than of the structure sheaf, which is what the graded-ideal
machinery of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Basic.lean` consumes; the two are
identified chart by chart through `…RelativeProjTwists.TwistData.chartData`, and nothing here
needs that identification. -/
def closedIdealDegreeZero : ((twistSheafGradedAlgebra D).piece 0).Submodule :=
  Stacks.Algebraization.kernelSubmodule
    (restrictionToClosed i ((twistSheafGradedAlgebra D).piece 0))

/-- **A local section of the degree-zero twist lies in `ℐ_Z` exactly when it restricts to zero on
the closed subscheme.** -/
theorem mem_closedIdealDegreeZero_iff (V : (relativeProj A).scheme.Opens)
    (a : Γ((twistSheafGradedAlgebra D).piece 0, V)) :
    a ∈ (closedIdealDegreeZero D i).toSubmodule.obj (op V) ↔
      (restrictionToClosed i ((twistSheafGradedAlgebra D).piece 0)).app V a = 0 :=
  AlgebraicGeometry.mem_kernelSubmodule_iff _ V a

/-- **`ℐ_Z` is quasi-coherent**: it is the sectionwise kernel of a morphism of quasi-coherent
modules. -/
theorem isQuasicoherent_closedIdealDegreeZero [IsClosedImmersion i] :
    (((closedIdealDegreeZero D i).toSheafOfModules :
      (relativeProj A).scheme.Modules)).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_kernelSubmodule _ ((twistSheafGradedAlgebra D).isQuasicoherent 0)
    (isQuasicoherent_pushforward_pullback i _)

end ClosedSubscheme

/-! ### The graded ideal generated in degree zero by the ideal sheaf of a closed subscheme -/

variable (ℐ : ((twistSheafGradedAlgebra D).piece 0).Submodule)

/-- **The graded ideal of the twists generated in degree `0`** by an `𝒪`-submodule `ℐ` of the
degree-zero twist. For `ℐ` the ideal sheaf of a closed subscheme `i : Z ⟶ Proj_S(𝒜)` this is the
graded ideal `d ↦ ℐ_Z · 𝒪(d)` whose quotient is `d ↦ (i_*𝒪_Z)(d)`. -/
def closedGradedIdeal : GradedIdeal (twistSheafGradedAlgebra D) :=
  gradedIdealGeneratedByDegree (twistSheafGradedAlgebra D) ℐ

/-- **`ℐ · 𝒪(d)` is quasi-coherent in every degree, so the quotient by it is data of
Situation 01NN.** This is the hypothesis `hqcZ` of the chain below, discharged for a
quasi-coherent `ℐ`; it is
`…RelativeProjGradedIdeal.isQuasicoherentQuotPieces_gradedIdealGeneratedByDegree` at the twists. -/
theorem isQuasicoherentQuotPieces_closedGradedIdeal
    (hqc : (((ℐ.toSheafOfModules : (relativeProj A).scheme.Modules))).IsQuasicoherent) :
    IsQuasicoherentQuotPieces (twistSheafGradedAlgebra D) (closedGradedIdeal D ℐ) :=
  isQuasicoherentQuotPieces_gradedIdealGeneratedByDegree (twistSheafGradedAlgebra D) ℐ hqc

/-- **The hypothesis `hqcZ` at the ideal sheaf of a closed subscheme, with nothing assumed.**
`ℐ_Z` is quasi-coherent by `isQuasicoherent_closedIdealDegreeZero`, so the graded ideal
`d ↦ ℐ_Z · 𝒪(d)` has quasi-coherent pieces and the whole chain below — Tag 0801's `ψ`, its graded
ideal, the quotient `𝒜/ℐ` and the closed immersion `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` — carries no
hypothesis beyond the tag's own. -/
theorem isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero
    {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) [IsClosedImmersion i] :
    IsQuasicoherentQuotPieces (twistSheafGradedAlgebra D)
      (closedGradedIdeal D (closedIdealDegreeZero D i)) :=
  isQuasicoherentQuotPieces_closedGradedIdeal D _ (isQuasicoherent_closedIdealDegreeZero D i)

variable (hqcZ : IsQuasicoherentQuotPieces (twistSheafGradedAlgebra D) (closedGradedIdeal D ℐ))

/-- **The graded algebra `d ↦ (i_*𝒪_Z)(d)` on `Proj_S(𝒜)`**: the degreewise quotient of the
twists by the graded ideal generated in degree `0` by the ideal sheaf of `Z`. -/
def restrictedTwistAlgebra : SheafGradedAlgebra (relativeProj A).scheme :=
  quotSheafGradedAlgebra (twistSheafGradedAlgebra D) (closedGradedIdeal D ℐ) hqcZ

/-- **The quotient homomorphism `q : ⨁_d 𝒪(d) ⟶ ⨁_d (i_*𝒪_Z)(d)`.** -/
def restrictionHom :
    SheafGradedAlgebraHom (twistSheafGradedAlgebra D) (restrictedTwistAlgebra D ℐ hqcZ) :=
  quotMk (twistSheafGradedAlgebra D) (closedGradedIdeal D ℐ) hqcZ

/-- **A homogeneous local section of the twists dies in `(i_*𝒪_Z)(n)` exactly when it lies in
`ℐ_Z · 𝒪(n)`.** -/
theorem restrictionHom_app_eq_zero_iff (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (a : Γ((twistSheafGradedAlgebra D).piece n, V)) :
    ((restrictionHom D ℐ hqcZ).app n).app V a = 0 ↔
      a ∈ ((closedGradedIdeal D ℐ).piece n).toSubmodule.obj (op V) :=
  quotMkApp_app_eq_zero_iff (twistSheafGradedAlgebra D) (closedGradedIdeal D ℐ) n V a

/-! ### Tag 0801's homomorphism and its graded ideal -/

section QuasiCompact

variable [QuasiCompact (relativeProj A).toBase]

/-- **The target of Tag 0801's homomorphism**: `⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))`, as sheaf-level
graded algebra data on `S`.

Quasi-coherence of the direct images is not a hypothesis: it is Tag 01LC for the quasi-compact
quasi-separated structure morphism, by `isQuasicoherent_pushforward_piece`. -/
def closedTwistTarget : SheafGradedAlgebra S :=
  pushforwardNonnegSheafGradedAlgebra (relativeProj A).toBase
    (ofSheafGradedAlgebra (restrictedTwistAlgebra D ℐ hqcZ))
    (isCommutative_ofSheafGradedAlgebra _)
    (isQuasicoherent_pushforward_piece (restrictedTwistAlgebra D ℐ hqcZ))

/-- **The truncated direct image of the quotient homomorphism**,
`⨁_{d ≥ 0} p_*(𝒪(d)) ⟶ ⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))`. -/
def pushforwardRestrictionHom :
    SheafGradedAlgebraHom (twistTarget D (isQuasicoherent_pushforward_twist D))
      (closedTwistTarget D ℐ hqcZ) :=
  pushforwardNonnegHom (relativeProj A).toBase D.algebra
    (ofSheafGradedAlgebra (restrictedTwistAlgebra D ℐ hqcZ)) D.mul_comm
    (isQuasicoherent_pushforward_twist D)
    (isCommutative_ofSheafGradedAlgebra _)
    (isQuasicoherent_pushforward_piece (restrictedTwistAlgebra D ℐ hqcZ))
    (fun n => (restrictionHom D ℐ hqcZ).app (n : ℤ))
    (fun i j W a b => (restrictionHom D ℐ hqcZ).app_mul (i : ℤ) (j : ℤ) W a b)
    (fun W => (restrictionHom D ℐ hqcZ).app_one W)

/-- **Tag 0801's homomorphism** `ψ : 𝒜 ⟶ ⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))`: the homogeneous-section
map of the relative Proj followed by the restriction to the closed subscheme. -/
def psiClosedHom : SheafGradedAlgebraHom A (closedTwistTarget D ℐ hqcZ) :=
  (pushforwardRestrictionHom D ℐ hqcZ).comp (psiHom D (isQuasicoherent_pushforward_twist D))

/-- **Tag 0801's graded ideal `ℐ`**: the degreewise kernel of `ψ`, the homogeneous local sections
of `𝒜` that vanish on the closed subscheme. Its pieces are quasi-coherent with no further
hypothesis, by `…RelativeProjGradedIdeal.isQuasicoherent_kernelGradedIdeal_piece`. -/
def closedVanishingIdeal : GradedIdeal A :=
  kernelGradedIdeal (psiClosedHom D ℐ hqcZ)

/-- **Tag 0801's kernel clause.** A homogeneous local section of `𝒜` lies in `ℐ` exactly when its
image in `p_*((i_*𝒪_Z)(n))` vanishes. -/
theorem mem_closedVanishingIdeal_iff (n : ℤ) (U : S.Opens) (a : Γ(A.piece n, U)) :
    a ∈ ((closedVanishingIdeal D ℐ hqcZ).piece n).toSubmodule.obj (op U) ↔
      ((psiClosedHom D ℐ hqcZ).app n).app U a = 0 :=
  mem_kernelGradedIdeal_iff (psiClosedHom D ℐ hqcZ) n U a

/-- **The quotient `𝒜/ℐ`** of Tag 0801, the `target` clause of
`…RelativeProjGradedIdeal.GradedQuotientPresentation`. -/
def closedQuotient : SheafGradedAlgebra S :=
  quotByKernel (psiClosedHom D ℐ hqcZ)

/-- **The quotient homomorphism `𝒜 ⟶ 𝒜/ℐ`**, the `hom` clause. -/
def closedQuotientMk : SheafGradedAlgebraHom A (closedQuotient D ℐ hqcZ) :=
  quotMkKernel (psiClosedHom D ℐ hqcZ)

/-- **The quotient homomorphism is degreewise surjective on the sections over the affine opens of
the base**, the `surjective` clause. -/
theorem surjectiveOnAffineSections_closedQuotientMk :
    ProjBundleSurjection.SurjectiveOnAffineSections (closedQuotientMk D ℐ hqcZ) :=
  surjectiveOnAffineSections_quotMkKernel (psiClosedHom D ℐ hqcZ)

/-- **`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`**, the morphism the `iso_comp` clause compares against. -/
def closedAmbientHom :
    (relativeProj (closedQuotient D ℐ hqcZ)).scheme ⟶ (relativeProj A).scheme :=
  kernelAmbientHom (psiClosedHom D ℐ hqcZ)

/-- **`Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.** -/
theorem isClosedImmersion_closedAmbientHom :
    IsClosedImmersion (closedAmbientHom D ℐ hqcZ) :=
  isClosedImmersion_kernelAmbientHom (psiClosedHom D ℐ hqcZ)

/-- **A homogeneous local section of `𝒜` dies in `𝒜/ℐ` exactly when it vanishes on the closed
subscheme**, over every open of the base. -/
theorem closedQuotientMk_app_eq_zero_iff (n : ℤ) (U : S.Opens) (a : Γ(A.piece n, U)) :
    ((closedQuotientMk D ℐ hqcZ).app n).app U a = 0 ↔
      ((psiClosedHom D ℐ hqcZ).app n).app U a = 0 :=
  quotMkKernel_app_eq_zero_iff (psiClosedHom D ℐ hqcZ) n U a

end QuasiCompact

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
