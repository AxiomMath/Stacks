module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Descent of finite presentation on the site along an fpqc covering

Stacks 03DL(7) has two renderings in this development: Mathlib's
`SheafOfModules.IsFinitePresentation`, a quasi-coherence datum all of whose presentations are
finite, and `SheafOfModules.IsFinitePresentationOnSite`, which asks for a covering of every
object on whose members the module has a finite global presentation.  The second implies the
first by `SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'`.  This file proves
the converse, on any site whose slices and iterated slices carry the two sheafification
instances, and deduces the on-site form of Stacks 060V for algebraic spaces from the form
`AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc` proves for Mathlib's predicate.

## Main results

* `Stacks.SheafOfModules.exists_finitePresentation_of_overOver`: a finite presentation of the
  restriction of `M.over U` to `Z : Over U` is a finite presentation of `M.over Z.left`.
* `Stacks.SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`: finite
  presentation in Mathlib's sense implies finite presentation on the site.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_pullback_fpqc`: **Stacks 060V** for
  `SheafOfModules.IsFinitePresentationOnSite`.

## References

* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), HasSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite presentation of the restriction of `M.over U` to `Z : Over U` is a finite
presentation of `M.over Z.left`, read through
`Stacks.SheafOfModules.Site.overOverEquivalence`.  This is the converse of
`Stacks.SheafOfModules.exists_finitePresentation_overOver`. -/
theorem exists_finitePresentation_of_overOver (M : _root_.SheafOfModules.{w} R) (U : C)
    (Z : Over U) (Q : ((M.over U).over Z).Presentation) [Q.IsFinite] :
    ∃ P : (M.over Z.left).Presentation, P.IsFinite := by
  have hpc : PreservesColimitsOfSize.{w, w} (Site.overOverEquivalence (R := R) U Z).inverse :=
    Adjunction.isEquivalence_preservesColimits _
  have hfc : PreservesFiniteColimits (Site.overOverEquivalence (R := R) U Z).inverse :=
    inferInstance
  have hfin : (LocalCokernel.mapFinitePresentation Q
      (Site.overOverEquivalence (R := R) U Z).inverse (Iso.refl _)).IsFinite :=
    LocalCokernel.mapFinitePresentation_isFinite Q
      (Site.overOverEquivalence (R := R) U Z).inverse (Iso.refl _)
  exact ⟨(LocalCokernel.mapFinitePresentation Q
    (Site.overOverEquivalence (R := R) U Z).inverse (Iso.refl _)).ofIsIso
      (Site.overOverIso M U Z).hom, inferInstance⟩

/-- **Finite presentation in the sense of Mathlib implies finite presentation on the site.**
Over an object `U`, the restriction `M.over U` is of finite presentation by
`Stacks.SheafOfModules.isFinitePresentation_over`; a quasi-coherence datum witnessing it is a
family of objects over `U` covering the final object of the slice, each carrying a finite
presentation of the restriction, which is a finite presentation of `M` over the underlying
object by `Stacks.SheafOfModules.exists_finitePresentation_of_overOver`, hence a finite global
presentation by `SheafOfModules.HasFiniteGlobalPresentation.of_presentation'`.  The family
covers `U` because it covers the final object of the slice over `U`. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation (M : _root_.SheafOfModules.{w} R)
    (hM : M.IsFinitePresentation) : M.IsFinitePresentationOnSite := by
  refine ⟨fun U => ?_⟩
  have hMU := isFinitePresentation_over M hM U
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (M.over U)
  refine ⟨ULift.{max u v} q.I, fun k => (q.X k.down).left, fun k => (q.X k.down).hom, ?_,
    fun k => ?_⟩
  · have hcov := q.coversTop (Over.mk (𝟙 U))
    rw [GrothendieckTopology.mem_over_iff] at hcov
    refine J.superset_covering ?_ hcov
    intro Y g hg
    rw [Sieve.overEquiv_iff] at hg
    obtain ⟨k, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨ULift.up k, a.left, ?_⟩
    exact (Category.comp_id g).symm.trans (Over.w a).symm
  · have := hq.isFinite_presentation k.down
    obtain ⟨P, hP⟩ := exists_finitePresentation_of_overOver M U (q.X k.down) (q.presentation k.down)
    exact _root_.SheafOfModules.HasFiniteGlobalPresentation.of_presentation' P hP

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 060V, for finite presentation on the site.**  Let `F` be a quasi-coherent
`𝒪_X`-module on an algebraic space `X` and let `{f i : X i ⟶ X}` be an fpqc covering such that
each `f i ^* F` is of finite presentation on the small étale site of `X i`.  Then `F` is of
finite presentation on the small étale site of `X`.

The two renderings of Stacks 03DL(7) are equivalent on the small étale site of an algebraic
space, by `SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` and
`Stacks.SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`, so this is
`AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc` read through them. -/
theorem isFinitePresentationOnSite_of_pullback_fpqc {I : Type v} {X : AlgebraicSpaces B S hS}
    (Xᵢ : I → AlgebraicSpaces B S hS) (f : ∀ i, Xᵢ i ⟶ X)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (hfp : ∀ i, ((modulePullback B S hS (f i)).obj F).IsFinitePresentationOnSite) :
    F.IsFinitePresentationOnSite :=
  Stacks.SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation F
    (isFinitePresentation_of_pullback_fpqc B S hS Xᵢ f F hF hf fun i ↦
      _root_.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ (hfp i))

end AlgebraicGeometry.Space

end
