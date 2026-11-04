module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Relative

/-!
# The third condition of Stacks 067Y, from the comparison of Stacks 09VF

`AlgebraicGeometry.pseudoCoherent_tfae` proves the equivalence of conditions (1) and (2) of
Stacks 067Y. Condition (3), that `f` is locally of finite type and `𝒪_X` is pseudo-coherent
relative to `S`, is relative pseudo-coherence of an object of the derived category of a scheme
over a base, `AlgebraicGeometry.Scheme.Hom.IsModulePseudoCoherent` (Stacks 09UI). What connects
it to condition (2) is the comparison the source invokes, namely Stacks 09VF — relative
`m`-pseudo-coherence of an object of `D_{QCoh}(𝒪_X)` is the same as relative
`m`-pseudo-coherence of the complexes `RΓ(U, E)` over `Γ(S, V)` for all compatible pairs of
affine opens — together with Stacks 09UJ, which is what turns the affine open coverings of
Stacks 09UI into all compatible affine pairs.

This file isolates exactly that comparison as a named hypothesis,
`AlgebraicGeometry.RelativeStructureSheafComparison`, at the one object it is needed for, and
derives the full three-condition form of Stacks 067Y from it. The hypothesis is **no longer
outstanding**: it is proved with no hypotheses as
`AlgebraicGeometry.relativeStructureSheafComparison` in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison`, by an entirely algebraic
argument, and the three-condition form of Stacks 067Y is therefore unconditional there, as
`AlgebraicGeometry.pseudoCoherent_tfae_three`. The results below are kept in their conditional
form because they are what that module consumes, and because they separate the formal unwinding
of the definitions from the mathematics of the comparison.

## Main results

* `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison`: given the
  comparison, condition (2) of Stacks 067Y is equivalent to its condition (3).
* `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`: the three conditions of
  Stacks 067Y, in the shape of `AlgebraicGeometry.pseudoCoherent_tfae`, given the comparison.

## Implementation notes

The hypothesis `relativeComparison` is the conjunction of Stacks 09VF and Stacks 09UJ
specialised to the structure sheaf: for every witness that `f` is locally of finite type and
every `m`, relative `m`-pseudo-coherence of `𝒪_X` over `S` is equivalent to relative
`m`-pseudo-coherence of `Γ(X, U)`, as a module over itself, with respect to `Γ(S, V)`, for every
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`. Two identifications of the source are folded into
this shape: that `𝒪_X` lies in `D_{QCoh}(𝒪_X)`, and that on an affine open `U` the complex
`RΓ(U, 𝒪_X)` is `Γ(X, U)` in degree zero. Neither is a weakening — both are instances of the
source's own hypotheses on `E` — but both are the reason the hypothesis is stated about
`Γ(X, U)` rather than about a derived sections functor. That shape is what makes the hypothesis
provable by commutative algebra alone, which is how
`AlgebraicGeometry.relativeStructureSheafComparison` discharges it.

Quantifying over the witness of `LocallyOfFiniteType f` rather than taking it as an instance is
what lets the hypothesis be used in both directions: condition (2) does not assume local
finiteness of type, it produces it, through
`AlgebraicGeometry.locallyOfFiniteType_of_forall_appLE_pseudoCoherent`. Since
`AlgebraicGeometry.LocallyOfFiniteType` is a `Prop`, the choice of witness is immaterial.

Neither result here carries a `stacks` tag, because both are conditional on
`AlgebraicGeometry.RelativeStructureSheafComparison`. The tag for the whole of Stacks 067Y sits
on the unconditional `AlgebraicGeometry.pseudoCoherent_tfae_three`, and
`AlgebraicGeometry.pseudoCoherent_tfae` carries it for the equivalence of (1) and (2).

## References

* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The content of Stacks 09VF and Stacks 09UJ at the structure sheaf: for `f` locally of finite
type, relative `m`-pseudo-coherence of `𝒪_X` over `S` in the sense of Stacks 09UI holds exactly
when, for every compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, the ring `Γ(X, U)` is
`m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`.

This is the hypothesis of the results below; it is stated as an abbreviation so that they and
its proof agree on its shape. It is proved, with no hypotheses, as
`AlgebraicGeometry.relativeStructureSheafComparison`. -/
public abbrev RelativeStructureSheafComparison {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (hft : LocallyOfFiniteType f) (m : ℤ),
    letI := hft
    Scheme.Hom.IsModulePseudoCoherentFrom f (SheafOfModules.unit X.ringCatSheaf) m ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
        (e : U ≤ f ⁻¹ᵁ V),
        letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
        letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
        PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom
          (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) m

/-- **Stacks 067Y, the equivalence of (2) and (3), conditionally on Stacks 09VF and
Stacks 09UJ.** A morphism of schemes is pseudo-coherent — condition (2) of Stacks 067Y, which is
`AlgebraicGeometry.PseudoCoherent` — if and only if it is locally of finite type and `𝒪_X` is
pseudo-coherent relative to `S`, which is condition (3).

The hypothesis is `AlgebraicGeometry.RelativeStructureSheafComparison`, the comparison of
Stacks 09VF and Stacks 09UJ at the structure sheaf, which is proved unconditionally as
`AlgebraicGeometry.relativeStructureSheafComparison`; the unconditional form of this statement is
`AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`. Everything else is the unwinding
of the definition of a pseudo-coherent ring map performed in
`AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType_and_relative`. -/
public theorem pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison
    (hcomp : RelativeStructureSheafComparison f) :
    PseudoCoherent f ↔
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf) := by
  rw [pseudoCoherent_iff_locallyOfFiniteType_and_relative]
  constructor
  · rintro ⟨hft, h⟩
    exact ⟨hft, fun m ↦ (hcomp hft m).mpr fun U hU V hV e ↦ h U hU V hV e m⟩
  · rintro ⟨hft, h⟩
    exact ⟨hft, fun U hU V hV e m ↦ (hcomp hft m).mp (h m) U hU V hV e⟩

/-- **Stacks 067Y, conditionally on Stacks 09VF and Stacks 09UJ.** The three equivalent
conditions of Stacks 067Y, in the shape of `AlgebraicGeometry.pseudoCoherent_tfae`: an affine
open covering of the base together with an affine open covering of the inverse image of each of
its members on which the maps on sections are pseudo-coherent ring maps; the same condition at
every compatible pair of affine opens; and local finiteness of type together with relative
pseudo-coherence of `𝒪_X` over `S`.

The hypothesis is `AlgebraicGeometry.RelativeStructureSheafComparison`; the equivalence of the
first two conditions is `AlgebraicGeometry.pseudoCoherent_tfae` and needs none of it. Feeding the
hypothesis the unconditional `AlgebraicGeometry.relativeStructureSheafComparison` gives
`AlgebraicGeometry.pseudoCoherent_tfae_three`, which is where the `067Y` tag for the whole lemma
sits. -/
public theorem pseudoCoherent_tfae_of_relativeComparison
    (hcomp : RelativeStructureSheafComparison f) :
    let pseudoCoherentOn := fun (V : S.Opens) (U : X.Opens)
        (h : U ≤ f ⁻¹ᵁ V) ↦
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U h).hom.toAlgebra
      Algebra.PseudoCoherent Γ(S, V) Γ(X, U)
    List.TFAE [
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i, pseudoCoherentOn (V j) (U i)
                ((le_iSup U i).trans hU.le),
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∀ (h : U ≤ f ⁻¹ᵁ V), pseudoCoherentOn V U h,
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf)] := by
  intro pseudoCoherentOn
  have h23 : (∀ (U : X.Opens), IsAffineOpen U →
      ∀ (V : S.Opens), IsAffineOpen V →
        ∀ (h : U ≤ f ⁻¹ᵁ V), pseudoCoherentOn V U h) ↔
      ∃ hft : LocallyOfFiniteType f,
        let := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf) := by
    rw [← pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison f hcomp,
      pseudoCoherent_iff]
    exact ⟨fun h {V} hV {U} hU e ↦ h U hU V hV e, fun h U hU V hV e ↦ h hV hU e⟩
  tfae_have 1 ↔ 2 := (pseudoCoherent_tfae f).out 1 2
  tfae_have 2 ↔ 3 := h23
  tfae_finish

end AlgebraicGeometry

end
