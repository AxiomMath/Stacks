module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.CategoryTheory.ObjectProperty.Slice

/-!
# Localization of the étale sites of an algebraic space at a chart

Let `X → Y` be an étale scheme chart of an algebraic space `Y`. The small étale site of `X`
is the localization of the small étale site of `Y` at `X` (Tag 04M0); here that comparison is
upgraded in two directions. It identifies the structure sheaves, so that the comparison is one
of *ringed* sites; and it restricts to the affine étale sites when the chart is affine, again
compatibly with the structure sheaves.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedEquivalenceOverChart`: the localization equivalence
  of small étale sites identifies the two structure presheaves.
* `AlgebraicGeometry.Space.affineEtaleEquivalenceOverChart`: the affine étale site of an
  affine étale chart is the localization of the affine étale site of its target.
* `AlgebraicGeometry.Space.affineEtaleRingedEquivalenceOverChart`: that affine comparison
  also identifies the two structure presheaves.
* `AlgebraicGeometry.Space.AffineEtale.topology_eq_inducedTopology`: the affine étale topology
  is the one induced from the small étale topology along the inclusion of the affine charts.

## Implementation notes

The source states these comparisons as equalities of sites. They are rendered as equivalences
of categories together with the equality of the induced topology, of the functors to the big
fppf site, and — in the ringed statements — of the commutative-ring-valued structure
presheaves.

## References

* [Stacks Project, Tag 04M1](https://stacks.math.columbia.edu/tag/04M1)
* [Stacks Project, Tag 04M2](https://stacks.math.columbia.edu/tag/04M2)
* [Stacks Project, Tag 04M3](https://stacks.math.columbia.edu/tag/04M3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The small étale ringed site of an étale scheme chart `X → Y` of an
algebraic space is the localization of the ringed small étale site of `Y` at that chart: the
localization equivalence of Tag 04M0 matches the two structure presheaves, naturally in the
chart. -/
@[stacks 04M1]
theorem smallEtaleRingedEquivalenceOverChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y)
    (X : SmallEtale B S hS Y) :
    ∃ e : SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj X)) ≌ Over X,
      e.functor.inducedTopology ((SmallEtale.topology B S hS Y).over X) =
        SmallEtale.topology B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj X)) ∧
      (e.functor ⋙ Over.forget X ⋙ SmallEtale.toOver B S hS Y =
        SmallEtale.toOver B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj X))) ∧
      (e.functor.op ⋙ (Over.forget X).op ⋙ structurePresheaf B S hS Y =
        structurePresheaf B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj X))) := by
  obtain ⟨e, htop, htover, _hchart⟩ := smallEtaleEquivalenceOverChart B S hS Y _hY X
  refine ⟨e, htop, htover, ?_⟩
  show (((e.functor ⋙ Over.forget X ⋙ SmallEtale.toOver B S hS Y) ⋙
      BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ) =
    ((SmallEtale.toOver B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj X)) ⋙
      BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ)
  exact congrArg (fun F ↦ F.op ⋙ Scheme.Γ)
    (congrArg (fun F ↦ F ⋙ BigFppfOver.toScheme B S hS) htover)

/-- The inclusion of the affine charts of an algebraic space is cover dense for the small
étale topology. -/
private theorem isCoverDense_affineEtale_inclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (AffineEtale.inclusion B S hS F).IsCoverDense (SmallEtale.topology B S hS F) :=
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS F)
    (SmallEtale.topology B S hS F) (AffineEtale.inclusion B S hS F)

/-- The affine étale topology of an algebraic space is the topology induced on the affine
charts by the small étale topology; this is the topological half of Tag 04JS. -/
theorem AffineEtale.topology_eq_inducedTopology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    AffineEtale.topology B S hS F =
      (AffineEtale.inclusion B S hS F).inducedTopology (SmallEtale.topology B S hS F) := by
  have := isCoverDense_affineEtale_inclusion B S hS F hF
  ext X R
  rw [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense]
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  exact Functor.IsDenseSubsite.functorPushforward_mem_iff.symm

/-- The affine étale site of an affine étale chart `X → Y` of an algebraic
space is the localization of the affine étale site of `Y` at that chart, by an equivalence
preserving both the topology and the underlying objects of the big fppf site. -/
@[stacks 04M2]
theorem affineEtaleEquivalenceOverChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y)
    (X : AffineEtale B S hS Y) :
    ∃ e : AffineEtale B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) ≌ Over X,
      e.functor.inducedTopology ((AffineEtale.topology B S hS Y).over X) =
        AffineEtale.topology B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) ∧
      e.functor ⋙ Over.forget X ⋙ AffineEtale.toOver B S hS Y =
        AffineEtale.toOver B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) := by
  let Xs := (AffineEtale.inclusion B S hS Y).obj X
  obtain ⟨eSmall, hSmallTopology, hSmallUnderlying⟩ :=
    smallEtaleEquivalenceOverChart B S hS Y _hY Xs
  let Psrc : ObjectProperty
      (SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj Xs))) :=
    IsAffineChart B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj Xs))
  let Ptgt : ObjectProperty (SmallEtale B S hS Y) := IsAffineChart B S hS Y
  let Q := Ptgt.overLeft Xs
  have hProperty : Q.inverseImage eSmall.functor = Psrc := by
    funext A
    apply propext
    have hObj := congrFun (congrArg (fun F ↦ F.obj) hSmallUnderlying.1) A
    have hScheme := congrArg ((BigFppfOver.toScheme B S hS).obj) hObj
    have hScheme' :
        (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS Y).obj (eSmall.functor.obj A).left) =
          (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS
              (yoneda.obj ((SmallEtale.toOver B S hS Y).obj Xs))).obj A) := by
      simpa using hScheme
    show IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS Y).obj (eSmall.functor.obj A).left)) ↔
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS Y).obj Xs))).obj A))
    rw [hScheme']
  have : Q.IsClosedUnderIsomorphisms := by
    constructor
    intro Z W i hZ
    dsimp [Q, ObjectProperty.overLeft, Ptgt, IsAffineChart] at hZ ⊢
    have hi : IsIso i.hom.left := by
      show IsIso ((Over.forget Xs).map i.hom)
      infer_instance
    let f := (SmallEtale.toOver B S hS Y).map i.hom.left
    have : IsIso f := by
      dsimp [f]
      infer_instance
    exact (IsAffine.iff_of_isIso ((BigFppfOver.toScheme B S hS).map f)).mp hZ
  let eRest := eSmall.congrFullSubcategory hProperty
  let eAffine := eRest.trans (ObjectProperty.overLeftEquivalence Ptgt X)
  have hSmallTopology' :
      eSmall.functor.inducedTopology ((SmallEtale.topology B S hS Y).over Xs) =
        SmallEtale.topology B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) := by
    simpa [Xs, AffineEtale.toOver, AffineEtale.inclusion, SmallEtale.toOver,
      SmallEtale.inclusion] using hSmallTopology
  have hComp : eAffine.functor ⋙ Over.post (AffineEtale.inclusion B S hS Y) =
      Psrc.ι ⋙ eSmall.functor :=
    CategoryTheory.Functor.hext (fun _ ↦ rfl) (fun _ _ _ ↦ HEq.rfl)
  refine ⟨eAffine, ?_, ?_⟩
  · ext U R
    let U' : Psrc.FullSubcategory := U
    let R' : Sieve U' := R
    rw [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense,
      CategoryTheory.GrothendieckTopology.mem_over_iff]
    have hRep : IsAlgebraicSpace B S hS
        (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) :=
      isAlgebraicSpace_yoneda B S hS ((AffineEtale.toOver B S hS Y).obj X)
    have := isCoverDense_affineEtale_inclusion B S hS Y _hY
    have := isCoverDense_affineEtale_inclusion B S hS _ hRep
    rw [AffineEtale.topology_eq_inducedTopology B S hS Y _hY,
      AffineEtale.topology_eq_inducedTopology B S hS
        (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) hRep]
    simp only [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense]
    rw [← hSmallTopology', CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense,
      CategoryTheory.GrothendieckTopology.mem_over_iff, ← Sieve.overEquiv_functorPushforward_post]
    have hBase : (Over.post (AffineEtale.inclusion B S hS Y)).obj (eAffine.functor.obj U') =
        eSmall.functor.obj (Psrc.ι.obj U') := by
      simpa [Xs, Functor.comp_obj] using congrArg (fun F ↦ F.obj U') hComp
    have hBase' : (Over.post (AffineEtale.inclusion B S hS Y)).obj (eAffine.functor.obj U') =
        eSmall.functor.obj ((AffineEtale.inclusion B S hS
          (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X))).obj U) := by
      simpa [Xs, Psrc, AffineEtale.inclusion, SmallEtale.inclusion] using hBase
    have hCompPush :
        Sieve.functorPushforward
            (eAffine.functor ⋙ Over.post (AffineEtale.inclusion B S hS Y)) R' =
          Sieve.functorPushforward (Psrc.ι ⋙ eSmall.functor) R' := by
      cases hComp
      rfl
    have hSieve :
        Sieve.functorPushforward (Over.post (AffineEtale.inclusion B S hS Y))
            (Sieve.functorPushforward eAffine.functor R') =
          Sieve.functorPushforward eSmall.functor (Sieve.functorPushforward Psrc.ι R') := by
      rw [← Sieve.functorPushforward_comp, hCompPush, Sieve.functorPushforward_comp]
    have hSieve' :
        Sieve.functorPushforward (Over.post (AffineEtale.inclusion B S hS Y))
            (Sieve.functorPushforward eAffine.functor R) =
          Sieve.functorPushforward eSmall.functor (Sieve.functorPushforward Psrc.ι R) := by
      simpa [U', R'] using hSieve
    cases hBase'
    rw [hSieve']
    rfl
  · have hUnderlying := congrArg (fun F ↦ Psrc.ι ⋙ F) hSmallUnderlying.1
    calc
      eAffine.functor ⋙ Over.forget X ⋙ AffineEtale.toOver B S hS Y =
          eAffine.functor ⋙ Over.post (AffineEtale.inclusion B S hS Y) ⋙
            Over.forget Xs ⋙ SmallEtale.toOver B S hS Y := rfl
      _ = Psrc.ι ⋙ eSmall.functor ⋙ Over.forget Xs ⋙ SmallEtale.toOver B S hS Y := by
          simpa [Functor.assoc] using
            congrArg (fun F ↦ F ⋙ Over.forget Xs ⋙ SmallEtale.toOver B S hS Y) hComp
      _ = AffineEtale.toOver B S hS
            (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) := by
        simpa [Xs, Psrc, AffineEtale.toOver, AffineEtale.inclusion, SmallEtale.toOver,
          SmallEtale.inclusion] using hUnderlying

/-- The affine étale ringed site of an affine étale chart `X → Y` of an
algebraic space is the localization of the ringed affine étale site of `Y` at that chart: the
equivalence of Tag 04M2 matches the two structure presheaves, naturally under restriction. -/
@[stacks 04M3]
theorem affineEtaleRingedEquivalenceOverChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y)
    (X : AffineEtale B S hS Y) :
    ∃ e : AffineEtale B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) ≌ Over X,
      e.functor.inducedTopology ((AffineEtale.topology B S hS Y).over X) =
        AffineEtale.topology B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X)) ∧
      (e.functor ⋙ Over.forget X ⋙ AffineEtale.toOver B S hS Y =
        AffineEtale.toOver B S hS (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X))) ∧
      (e.functor.op ⋙ (Over.forget X).op ⋙ (AffineEtale.inclusion B S hS Y).op ⋙
          structurePresheaf B S hS Y =
        (AffineEtale.inclusion B S hS
          (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X))).op ⋙
          structurePresheaf B S hS
            (yoneda.obj ((AffineEtale.toOver B S hS Y).obj X))) := by
  obtain ⟨e, htop, hfun⟩ := affineEtaleEquivalenceOverChart B S hS Y _hY X
  refine ⟨e, htop, hfun, ?_⟩
  have hstruct :=
    congrArg (fun F ↦ F.op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ) hfun
  refine CategoryTheory.Functor.ext (fun U ↦ ?_) (fun U V f ↦ ?_)
  · simpa [structurePresheaf, AffineEtale.toOver, AffineEtale.inclusion] using
      congrArg (fun F ↦ F.obj U) hstruct
  · simpa [structurePresheaf, AffineEtale.toOver, AffineEtale.inclusion] using
      CategoryTheory.Functor.congr_hom hstruct f

end AlgebraicGeometry.Space

end
