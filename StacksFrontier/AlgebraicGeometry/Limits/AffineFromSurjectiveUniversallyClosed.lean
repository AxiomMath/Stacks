module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.SmallSystem
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FilteredLimit
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination

/-!
# Affineness of the target of a surjective universally closed morphism

[Stacks, Tag 05YU] asserts that a scheme `S` admitting a surjective universally closed
morphism `f : X ⟶ S` from an affine scheme `X` is affine.  This file proves it, in two steps:
a reduction of `f` to an integral morphism over a separated, quasi-compact and quasi-separated
base, and a limit argument over an inverse-limit presentation of that integral morphism.

The first half is unconditional.  Separatedness of `S` descends along `f` from the affine, hence
separated, source, so `f` is an affine morphism; being affine and universally closed it is
integral, and `S` is quasi-compact because it is the image of the quasi-compact `X` and
quasi-separated because it is separated.  If `f` is in addition locally of finite type it is
then finite, and [Stacks, Tag 01ZT] already gives the conclusion.

The second half is the limit argument.  Given a presentation of the integral morphism `f` as the
inverse limit of finite morphisms to `S`, one of the stages is affine because the limit is, and
every stage receives `X`, so every stage is surjective over `S`; [Stacks, Tag 01ZT] applied to
that stage gives affineness of `S`.

## Main results

* `Stacks.AffineFromUniversallyClosed.isIntegralHom_of_isAffine_surjective_universallyClosed`:
  a surjective universally closed morphism out of an affine scheme is integral.
* `Stacks.AffineFromUniversallyClosed`'s
  `isAffine_of_surjective_universallyClosed_of_locallyOfFiniteType`: the case of
  [Stacks, Tag 05YU] in which the morphism is locally of finite type.
* `Stacks.AffineFromUniversallyClosed.isAffine_of_integralLimitPresentation`: a scheme carrying
  a surjective morphism from an affine scheme which is presented as an inverse limit of finite
  morphisms is affine.
* `Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed_of_h09YZ`:
  [Stacks, Tag 05YU] from [Stacks, Tag 09YZ].
* `Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed`:
  **[Stacks, Tag 05YU]**.

## Implementation notes

The hypothesis standing for [Stacks, Tag 09YZ] is the predicate
`AlgebraicGeometry.IntegralHasFinitePresentationLimit` already recorded in the library, and the
data it produces is `AlgebraicGeometry.IntegralLimitPresentation`.

The inverse-limit presentation the proposition needs is weaker than [Stacks, Tag 09YZ]: only
finiteness of the stages is used, not their finite presentation.  It is assembled from part (1)
of [Stacks, Tag 0817], which presents the integral quasi-coherent algebra `f_* 𝒪_X` as a directed
colimit of finite quasi-coherent subalgebras over an index in the universe of the scheme
(`Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite`), and the relative
spectrum, which carries such a colimit of algebra sheaves to a limit of schemes over the base
(`Stacks.RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra`).

`isAffine_of_surjective_universallyClosed_of_h09YZ` is retained as the derivation of the
proposition from an arbitrary such presentation, which is how it reads off [Stacks, Tag 09YZ];
it is no longer the route to the proposition itself.

## References

* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AffineFromUniversallyClosed

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The unconditional reduction -/

/-- A morphism from an affine scheme to a separated scheme is an affine morphism. -/
theorem isAffineHom_of_isAffine_of_isSeparated [IsAffine X] [S.IsSeparated] :
    IsAffineHom f := by
  have h : IsAffineHom (f ≫ terminal.from S) := by
    rw [terminal.comp_from]
    infer_instance
  exact IsAffineHom.of_comp f (terminal.from S)

/-- A scheme receiving a surjective universally closed morphism from an affine scheme is
separated. -/
@[sga "3 V 7.4" "special case"]
theorem isSeparated_of_isAffine_surjective_universallyClosed [IsAffine X] [Surjective f]
    [UniversallyClosed f] : S.IsSeparated :=
  Scheme.isSeparated_of_surjective_universallyClosed f

/-- A scheme receiving a surjective morphism from an affine scheme is quasi-compact. -/
theorem compactSpace_of_isAffine_surjective [IsAffine X] [Surjective f] : CompactSpace S := by
  refine isCompact_univ_iff.mp ?_
  rw [← f.surjective.range_eq]
  exact isCompact_range f.continuous

/-- A surjective universally closed morphism out of an affine scheme is an affine morphism. -/
theorem isAffineHom_of_isAffine_surjective_universallyClosed [IsAffine X] [Surjective f]
    [UniversallyClosed f] : IsAffineHom f := by
  have : S.IsSeparated := isSeparated_of_isAffine_surjective_universallyClosed f
  exact isAffineHom_of_isAffine_of_isSeparated f

/-- A surjective universally closed morphism out of an affine scheme is integral: it is affine
because its target is separated, and an affine universally closed morphism is integral. -/
theorem isIntegralHom_of_isAffine_surjective_universallyClosed [IsAffine X] [Surjective f]
    [UniversallyClosed f] : IsIntegralHom f := by
  have : IsAffineHom f := isAffineHom_of_isAffine_surjective_universallyClosed f
  exact IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-! ### The limit argument -/

/-- If `f : X ⟶ S` is surjective with `X` affine and `S` quasi-compact and quasi-separated, and
`X` is the limit of a directed inverse system of schemes finite over `S` through which `f`
factors, then `S` is affine. -/
private theorem isAffine_of_isLimit_of_isFinite {J : Type u} [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] (D : Jᵒᵖ ⥤ Scheme.{u}) (st : D ⟶ (Functor.const Jᵒᵖ).obj S)
    (π : (Functor.const Jᵒᵖ).obj X ⟶ D) (hfin : ∀ i, IsFinite (st.app i))
    (hcompat : ∀ i, π.app i ≫ st.app i = f) (hlim : IsLimit (Cone.mk X π)) [IsAffine X]
    [Surjective f] [CompactSpace S] [QuasiSeparatedSpace S] : IsAffine S := by
  have : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := by
    intro i j g
    have : IsFinite (st.app j) := hfin j
    have hnat : D.map g ≫ st.app j = st.app i := by simp
    have : IsAffineHom (D.map g ≫ st.app j) := hnat ▸ (hfin i).toIsAffineHom
    exact IsAffineHom.of_comp (D.map g) (st.app j)
  have : ∀ i : Jᵒᵖ, CompactSpace (D.obj i) := by
    intro i
    have := hfin i
    have : CompactSpace (((Functor.const Jᵒᵖ).obj S).obj i) := by dsimp; infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace (st.app i)
  have : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i) := by
    intro i
    have := hfin i
    have : QuasiSeparatedSpace (((Functor.const Jᵒᵖ).obj S).obj i) := by dsimp; infer_instance
    exact quasiSeparatedSpace_of_quasiSeparated (st.app i)
  have : IsAffine (Cone.mk X π).pt := ‹IsAffine X›
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D (Cone.mk X π) hlim
  have : Surjective (st.app i) := by
    have : Surjective (π.app i ≫ st.app i) := by rw [hcompat i]; infer_instance
    exact Surjective.of_comp (π.app i) (st.app i)
  have := hfin i
  have : IsAffine (D.obj i) := hi
  exact AffineFromFiniteSurjective.isAffine_of_finite_surjective (st.app i)

/-- **The limit half of [Stacks, Tag 05YU].** Let `f : X ⟶ S` be surjective with `X` affine and
`S` quasi-compact and quasi-separated, presented as the inverse limit of finite morphisms of
finite presentation to `S`.  Then `S` is affine.

Some stage of the presentation is affine by [Stacks, Tag 01Z6], and `f` factors through it, so
that stage is a finite surjective cover of `S` by an affine scheme; [Stacks, Tag 01ZT] applies
to it.  Finite presentation of the stages is not used. -/
theorem isAffine_of_integralLimitPresentation (P : IntegralLimitPresentation f) [IsAffine X]
    [Surjective f] [CompactSpace S] [QuasiSeparatedSpace S] :
    IsAffine S := by
  let inst := P.indexPreorder
  have : Nonempty P.indexType := P.indexNonempty
  have : IsDirected P.indexType (· ≤ ·) := P.indexDirected
  exact isAffine_of_isLimit_of_isFinite f P.diagram P.structureMap P.limitCone P.stageFinite
    (fun i => (P.compatible i).symm) P.isLimit

/-! ### The case of a morphism locally of finite type -/

/-- A scheme receiving a surjective universally closed morphism locally of finite type from an
affine scheme is affine: such a morphism is integral, hence finite, so [Stacks, Tag 01ZT]
applies.  This is the case of [Stacks, Tag 05YU] in which no limit presentation is needed. -/
theorem isAffine_of_surjective_universallyClosed_of_locallyOfFiniteType [IsAffine X]
    [Surjective f] [UniversallyClosed f] [LocallyOfFiniteType f] : IsAffine S := by
  have : IsIntegralHom f := isIntegralHom_of_isAffine_surjective_universallyClosed f
  have : IsFinite f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨inferInstance, inferInstance⟩
  exact AffineFromFiniteSurjective.isAffine_of_finite_surjective f

/-! ### The proposition from its one missing input -/

/-- **[Stacks, Tag 05YU] from [Stacks, Tag 09YZ].** A scheme `S` receiving a surjective
universally closed morphism from an affine scheme is affine, granted that an integral morphism
over a quasi-compact quasi-separated base is an inverse limit of finite morphisms of finite
presentation.

That hypothesis is proved in this library only for an affine base, so this is not a proof of
Tag 05YU; the unconditional content is the reduction of `f` to an integral morphism over a
separated, quasi-compact and quasi-separated base, and the passage from such a limit
presentation to affineness of `S`. -/
theorem isAffine_of_surjective_universallyClosed_of_h09YZ [IsAffine X] [Surjective f]
    [UniversallyClosed f] (h09YZ : IntegralHasFinitePresentationLimit.{u}) :
    IsAffine S := by
  have : S.IsSeparated := isSeparated_of_isAffine_surjective_universallyClosed f
  have : CompactSpace S := compactSpace_of_isAffine_surjective f
  have : IsIntegralHom f := isIntegralHom_of_isAffine_surjective_universallyClosed f
  obtain ⟨P⟩ := h09YZ X S f inferInstance inferInstance inferInstance
  exact isAffine_of_integralLimitPresentation f P

/-! ### The proposition -/

/-- **[Stacks, Tag 05YU].** A scheme admitting a surjective universally closed morphism from an
affine scheme is affine.

By the reduction above the morphism is integral over a separated, quasi-compact and
quasi-separated base, so `f_* 𝒪_X` is an integral quasi-coherent sheaf of `𝒪_S`-algebras.  Part
(1) of [Stacks, Tag 0817] presents it as a directed colimit of finite quasi-coherent
subalgebras, indexed in the universe of the scheme, and the relative spectrum turns that colimit
into an inverse system of schemes finite over `S` whose limit is `X`.  One stage of that system
is affine by [Stacks, Tag 01Z6], and is surjective over `S` because `f` factors through it, so
[Stacks, Tag 01ZT] applies to it. -/
@[stacks 05YU]
theorem isAffine_of_surjective_universallyClosed [IsAffine X] [Surjective f]
    [UniversallyClosed f] : IsAffine S := by
  have : S.IsSeparated := isSeparated_of_isAffine_surjective_universallyClosed f
  have : CompactSpace S := compactSpace_of_isAffine_surjective f
  have hint : IsIntegralHom f := isIntegralHom_of_isAffine_surjective_universallyClosed f
  have haff : IsAffineHom f := isAffineHom_of_isAffine_surjective_universallyClosed f
  have hA : (AffineAlgebraEquivalence.pushforwardAlgebra f).IsIntegral :=
    fun U hU => ((isIntegralHom_iff f).mp hint).2 U hU
  obtain ⟨I, hIp, hIne, hIdir, F, t, ht, hFprop⟩ :=
    AlgebraicGeometry.FiniteSubalgebras.exists_small_isColimit_finite
      (AffineAlgebraEquivalence.pushforwardAlgebra f)
      (AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra f) hA
  obtain ⟨D, st, π, hlim, hcompat, htrans, hstaff, hiso⟩ :=
    RelativeSpec.exists_isLimit_of_isColimit_pushforwardAlgebra f F t ht fun i => (hFprop i).1
  have hstfin : ∀ i, IsFinite (st.app i) := by
    intro i
    have := hstaff i
    refine (FiniteAlgebraLimitPresentation.pushforwardAlgebra_isFinite_iff (st.app i)).mp ?_
    obtain ⟨e⟩ := hiso i
    exact FiniteAlgebraLimitPresentation.isFinite_of_iso e (hFprop i.unop).2
  exact isAffine_of_isLimit_of_isFinite f D st π hstfin hcompat hlim

end Stacks.AffineFromUniversallyClosed
