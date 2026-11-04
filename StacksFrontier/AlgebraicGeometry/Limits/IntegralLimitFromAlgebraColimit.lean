module

public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.SmallIndex
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.SmallSystem
public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FilteredLimit
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination

/-!
# An integral morphism as a limit of finite morphisms of finite presentation

Let `f : X ⟶ S` be an integral morphism of schemes with `S` quasi-compact and quasi-separated.
[Stacks, Tag 09YZ] exhibits `X` as the limit of a directed inverse system of schemes finite and
of finite presentation over `S`, and its proof is: the quasi-coherent algebra `f_* 𝒪_X` is
integral, part (2) of [Stacks, Tag 0817] writes it as a directed colimit of finite and finitely
presented quasi-coherent algebras, and the relative spectrum turns that colimit into the required
limit of schemes.

This file carries out everything in that proof **except** part (2) of [Stacks, Tag 0817], which
is isolated as the hypothesis
`Stacks.IntegralLimit.IntegralAlgebraHasFiniteFinitePresentationColimit`: the geometry is
`Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra`, and the finiteness and
finite presentation of each stage are read off its algebra.  The remaining hypothesis is in turn
reduced, in `integralAlgebraHasFiniteFinitePresentationColimit_of_isFinitelyPresentable`, to the
finite presentability of a finite and finitely presented quasi-coherent algebra as an object of
the category of algebra sheaves, which is [Stacks, Tag 01BS].

## Main definitions

* `Stacks.IntegralLimit.IntegralAlgebraHasFiniteFinitePresentationColimit` is part (2) of
  [Stacks, Tag 0817], with the index in the universe of the scheme, as a proposition.

## Main results

* `Stacks.IntegralLimit.pushforwardAlgebra_isIntegral`: the algebra `f_* 𝒪_X` of an integral
  morphism is integral.
* `Stacks.IntegralLimit.locallyOfFinitePresentation_of_isFinitePresentation`: an affine morphism
  whose algebra is of finite presentation is locally of finite presentation.  This is the
  converse of `Stacks.FiniteAlgebraLimitPresentation.pushforwardAlgebra_isFinitePresentation`.
* `Stacks.IntegralLimit.nonempty_integralLimitPresentation_of_algebraColimit`: **[Stacks, Tag
  09YZ] granted part (2) of [Stacks, Tag 0817]**, for a base that is merely quasi-compact and
  quasi-separated.
* `integralAlgebraHasFiniteFinitePresentationColimit_of_isFinitelyPresentable`: part (2) of
  [Stacks, Tag 0817] follows from part (1), [Stacks, Tag 086N] and the finite presentability of the
  stages.

## Superseded

`IntegralAlgebraHasFiniteFinitePresentationColimit` is **proved**, as
`Stacks.AlgebraicGeometry.Tag0817PartTwo.integralAlgebraHasFiniteFinitePresentationColimit`, so
`nonempty_integralLimitPresentation_of_algebraColimit` is unconditional; the general case of
[Stacks, Tag 09YZ] is
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`.  What was missing
was not [Stacks, Tag 01BS] for algebra sheaves, which is still absent, but the observation that
the splice needs presentability only along its own two cocones, where [Stacks, Tag 01ZC] answers.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached.** Every statement below whose content is a tag is
conditional: `nonempty_integralLimitPresentation_of_algebraColimit` on part (2) of
[Stacks, Tag 0817], and
`integralAlgebraHasFiniteFinitePresentationColimit_of_isFinitelyPresentable` on
`CategoryTheory.IsFinitelyPresentable` of the stages, which is [Stacks, Tag 01BS] and is not
proved in this library.  [Stacks, Tag 09YZ] itself, at a quasi-compact and quasi-separated base,
is unconditional and carries its attribute on
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which is
`nonempty_integralLimitPresentation_of_algebraColimit` below with its hypothesis discharged;
`AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine` is the affine-base case, which
is strictly weaker and likewise carries no attribute.

The two inputs that part (2) of [Stacks, Tag 0817] is composed of are both available with an
index in the universe of the scheme — part (1) as
`Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite` and [Stacks, Tag 086N]
as `Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation` — so
the universe in which the tag states its index costs nothing here.  What the two do not supply is
a transition map from a stage of the inner system chosen for one finite subalgebra to a stage of
the inner system chosen for a larger one; that is what finite presentability provides, through
`Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`.

## Implementation notes

`locallyOfFinitePresentation_of_isFinitePresentation` is proved by restricting to the affine
opens of the target, where the morphism becomes a morphism of affine schemes because it is
affine, so that `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine` applies; the comparison of
`AlgebraicGeometry.morphismRestrict_appTop` with the sections of the algebra is an isomorphism,
which `RingHom.finitePresentation_respectsIso` cancels.

The finiteness of a stage is read off its algebra by
`Stacks.FiniteAlgebraLimitPresentation.pushforwardAlgebra_isFinite_iff` and its finite
presentation by the lemma above; in both cases the algebra of the stage is identified with the
given member of the diagram by the isomorphism that
`Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra` returns.

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec

universe u

namespace Stacks.IntegralLimit

/-- The quasi-coherent algebra `f_* 𝒪_X` of an integral morphism is integral: its structural ring
map on the sections over an affine open is the map on sections of `f` there. -/
theorem pushforwardAlgebra_isIntegral {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] :
    (pushforwardAlgebra f).IsIntegral :=
  fun U hU => IsIntegralHom.isIntegral_app f U hU

/-- **An affine morphism whose algebra is of finite presentation is locally of finite
presentation.**  This is the converse of
`Stacks.FiniteAlgebraLimitPresentation.pushforwardAlgebra_isFinitePresentation`.

Finite presentation of a morphism is Zariski local on the target, and over an affine open of the
target the morphism is a morphism of affine schemes, where it is detected by its map on global
sections. -/
theorem locallyOfFinitePresentation_of_isFinitePresentation {Y S : Scheme.{u}} (g : Y ⟶ S)
    [IsAffineHom g] (h : (pushforwardAlgebra g).IsFinitePresentation) :
    LocallyOfFinitePresentation g := by
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation)
    (fun U : S.affineOpens => U.1) (iSup_affineOpens_eq_top S)]
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (g ⁻¹ᵁ U.1).toScheme := U.2.preimage g
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation),
    morphismRestrict_appTop]
  have hfp : RingHom.FinitePresentation (g.app (U.1.ι ''ᵁ ⊤)).hom := by
    have himg : U.1.ι ''ᵁ ⊤ = U.1 := by simp
    rw [himg]
    exact h U.1 U.2
  exact (RingHom.finitePresentation_respectsIso.cancel_right_isIso _ _).mpr hfp

/-- **Part (2) of [Stacks, Tag 0817], with the index in the universe of the scheme, as a
proposition.**  An integral quasi-coherent sheaf of commutative algebras on a quasi-compact and
quasi-separated scheme is the colimit of a directed system, indexed by a nonempty directed
preorder in that universe, of quasi-coherent algebras which are finite and of finite
presentation. -/
def IntegralAlgebraHasFiniteFinitePresentationColimit : Prop :=
  ∀ (S : Scheme.{u}) (_ : CompactSpace S) (_ : QuasiSeparatedSpace S) (A : AlgebraSheaf S),
    A.IsQuasicoherent → A.IsIntegral →
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (F : I ⥤ AlgebraSheaf S) (t : F ⟶ (Functor.const I).obj A)
        (_ : IsColimit (Cocone.mk A t)),
        ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧ (F.obj i).IsFinitePresentation

/-- **[Stacks, Tag 09YZ], granted part (2) of [Stacks, Tag 0817].**  An integral morphism to a
quasi-compact and quasi-separated scheme exhibits its source as the limit of a directed inverse
system of schemes finite and of finite presentation over that target.

The system is the one of relative spectra of the colimit presentation of `f_* 𝒪_X` supplied by
the hypothesis, through
`Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra`. -/
theorem nonempty_integralLimitPresentation_of_algebraColimit
    (h0817 : IntegralAlgebraHasFiniteFinitePresentationColimit.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty (IntegralLimitPresentation f) := by
  obtain ⟨I, _, _, _, F, t, hcolim, hF⟩ := h0817 S ‹_› ‹_› (pushforwardAlgebra f)
    (isQuasicoherent_pushforwardAlgebra f) (pushforwardAlgebra_isIntegral f)
  obtain ⟨D, st, π, hlim, hcompat, _, hst, hiso⟩ :=
    Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra f F t hcolim
      (fun i => (hF i).1)
  have hfin : ∀ i, IsFinite (st.app i) := by
    intro i
    have := hst i
    obtain ⟨e⟩ := hiso i
    exact (Stacks.FiniteAlgebraLimitPresentation.pushforwardAlgebra_isFinite_iff (st.app i)).mp
      (Stacks.FiniteAlgebraLimitPresentation.isFinite_of_iso e (hF i.unop).2.1)
  refine ⟨{
    indexType := I
    indexPreorder := inferInstance
    indexNonempty := inferInstance
    indexDirected := inferInstance
    diagram := D
    structureMap := st
    limitCone := π
    compatible := fun i => (hcompat i).symm
    isLimit := hlim
    stageFinite := hfin
    stageFinitePresentation := fun i => ?_ }⟩
  have := hst i
  have := hfin i
  obtain ⟨e⟩ := hiso i
  have hlfp : LocallyOfFinitePresentation (st.app i) :=
    locallyOfFinitePresentation_of_isFinitePresentation (st.app i)
      (Stacks.FiniteAlgebraLimitPresentation.isFinitePresentation_of_iso e (hF i.unop).2.2)
  exact ⟨hlfp, inferInstance, inferInstance⟩

/-- **Part (2) of [Stacks, Tag 0817] follows from part (1), [Stacks, Tag 086N] and the finite
presentability of the stages.**

Part (1) with a small index is
`Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite` and [Stacks, Tag 086N]
with a small index is
`Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation`; the two
are composed by `Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`, whose
hypothesis is the finite presentability assumed here and is [Stacks, Tag 01BS]. -/
theorem integralAlgebraHasFiniteFinitePresentationColimit_of_isFinitelyPresentable
    (hfp : ∀ (S : Scheme.{u}) (B : AlgebraSheaf S), B.IsQuasicoherent → B.IsFinite →
      B.IsFinitePresentation → IsFinitelyPresentable.{u} B) :
    IntegralAlgebraHasFiniteFinitePresentationColimit.{u} := by
  intro S hcompact hqs A hAqc hAint
  have := hcompact
  have := hqs
  obtain ⟨I, _, _, _, F, t, hcolim, hFfin⟩ :=
    Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite A hAqc hAint
  choose K hKpre hKne hKdir E s hs hE using fun i : I =>
    Stacks.FiniteAlgebraLimitPresentation.exists_small_isColimit_finite_finitePresentation
      S (F.obj i) (hFfin i).1 (hFfin i).2
  let _ : ∀ i, Preorder (K i) := hKpre
  have : ∀ i, Nonempty (K i) := hKne
  have : ∀ i, IsDirected (K i) (· ≤ ·) := hKdir
  have : ∀ i, IsFiltered (K i) := fun i => inferInstance
  exact Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf
    (K := K) (E := E) t s hcolim hs
    (Stacks.FinitelyPresentableComposition.twoStagePresentable_of_isFinitelyPresentable
      (K := K) (E := E) t s hcolim hs
      fun i k => hfp S ((E i).obj k) (hE i k).1 (hE i k).2.1 (hE i k).2.2)
    (fun B => B.IsQuasicoherent ∧ B.IsFinite ∧ B.IsFinitePresentation) (fun i k => hE i k)

end Stacks.IntegralLimit

end
