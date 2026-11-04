module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GlobalSlicingSequenceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreUnramifiedRegularSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedGlobalSections

/-!
# The slicing sequence of Stacks 06N3 as global functions on the algebraic space

The fibre hypothesis of **Stacks 06MD**,
`AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`, is about **global sections of the structure
sheaf of the algebraic space** `U` being sliced. What the slicing point of the chart construction
of **Stacks 06N3** produces is a regular sequence of *germs* on a scheme chart of `U`, and
realizing those germs as global sections is what the source's first shrinking of `U` is for.

This file does it with no shrinking, for a chart `U` which is **represented by an affine object
of the site** — which is how **Stacks 06FX** produces the smooth chart the construction starts
from. Two things make that possible:

* on an affine scheme the slicing sequence can be chosen among the **global** functions from the
  outset, `AlgebraicGeometry.exists_global_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`;
* for a **represented** algebraic space a global function on the representing scheme *is* a
  global section of the structure sheaf of the small étale site,
  `AlgebraicGeometry.Space.representedUnitSection`, the small étale site of a represented
  presheaf having the identity chart for a terminal object.

## Main results

* `AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`:
  global sections of the structure sheaf of a represented affine chart `U` whose germs on the
  chart of the fibre form a regular sequence **generating** the maximal ideal there, and whose
  images in the étale local ring `𝒪_{F, z̄}` form a regular sequence for **every** small étale
  neighbourhood of the image geometric point — the body of
  `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt` verbatim.

## Implementation notes

The chart square is taken against the identity chart of the representing object, so the morphism
of schemes it delivers is the chart's own structure morphism `q : V ⟶ U` and the value of a
global section on it is the pullback of the global function along `q`
(`AlgebraicGeometry.Space.eval_representedUnitSection`); the two readings of that pullback's germ
— as a germ of a pulled-back function and as the image of a germ under `q.stalkMap` — are
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`.

The passage from the chart-level regular sequence to the étale local ring is
`AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_of_isRegular_chartLocalRing`,
across the faithful flatness of **Stacks 05VP** and the square of local rings of **Stacks 05VU**;
nothing of that is redone here.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06N3**, which is no
tag of its own.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The slicing sequence of Stacks 06N3 as global sections on a represented affine chart.**
Let `ξ : F ⟶ U` be a morphism of algebraic spaces whose target is represented by an object `T`
of the site with **affine** underlying scheme, let `z` be a geometric point of `F`, and let a
small étale neighbourhood `N` of `z` lie over `T` by a morphism `p` of the site whose underlying
morphism of schemes `q : V ⟶ U` is locally of finite type and **unramified** at the point `v` of
`V` under `z`. If `𝒪_{V, v}` is **regular**, then there are `d = (𝔪_v).spanFinrank`
**global sections** of the structure sheaf of `U` whose germs at `v` — pulled back along `q` —
form a regular sequence **generating** `𝔪_v`, and whose images in the étale local ring
`𝒪_{F, z̄}` form a regular sequence for every small étale neighbourhood of the image geometric
point.

The second conclusion is the body of `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`, the
fibre hypothesis of **Stacks 06MD**; the first is what the unramifiedness criterion of
**Stacks 02GF** reads off the slice, through
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field`. No
shrinking of `U` intervenes: the sequence is chosen among the global functions of the affine
chart by
`AlgebraicGeometry.exists_global_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`, and
read as global sections of the structure sheaf by
`AlgebraicGeometry.Space.representedUnitSection`. -/
theorem exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine
    {T : BigFppfOver B S hS} (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ (⟨yoneda.obj T, hT⟩ : AlgebraicSpaces B S hS))
    {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (p : N.chart.obj.left ⟶ T) (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map p)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p)]
    (hunr : UnramifiedAt ((BigFppfOver.toScheme B S hS).map p)
      (chartPoint B S hS Fs.1 N))
    (hregular : IsRegularLocalRing (chartLocalRing B S hS Fs.1 N)) :
    ∃ fs : Fin (maximalIdeal (chartLocalRing B S hS Fs.1 N)).spanFinrank →
        (SheafOfModules.unit (structureRingSheaf B S hS
          (⟨yoneda.obj T, hT⟩ : AlgebraicSpaces B S hS))).sections,
      RingTheory.Sequence.IsRegular (chartLocalRing B S hS Fs.1 N)
          (List.ofFn fun i => (chartScheme N.chart).presheaf.germ ⊤
            (chartPoint B S hS Fs.1 N) trivial
            ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op).hom
              ((fs i).eval (op (idChart B S hS T))))) ∧
        Ideal.ofList (List.ofFn fun i => (chartScheme N.chart).presheaf.germ ⊤
            (chartPoint B S hS Fs.1 N) trivial
            ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op).hom
              ((fs i).eval (op (idChart B S hS T))))) =
          maximalIdeal (chartLocalRing B S hS Fs.1 N) ∧
        ∀ M : SmallEtaleNeighborhood (geometricPointMap ξ.hom z),
          RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
            (List.ofFn fun i => etaleLocalRingMap Fs.2 ξ.hom z
              (etaleLocalRingGerm B S hS (yoneda.obj T) (geometricPointMap ξ.hom z) (op M)
                ((fs i).eval (op M.chart)))) := by
  -- the slicing sequence as global functions on the affine chart
  obtain ⟨g, hgmem, hgreg, hgspan⟩ :=
    exists_global_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt
      ((BigFppfOver.toScheme B S hS).map p) (chartPoint B S hS Fs.1 N) hunr hregular
  -- their values on the identity chart are themselves
  have heval : ∀ i, (representedUnitSection B S hS T hT (g i)).eval
      (op (idChart B S hS T)) = g i := fun i =>
    (representedUnitSectionsEquiv_apply_eq_eval B S hS T hT _).symm.trans
      ((representedUnitSectionsEquiv B S hS T hT).apply_symm_apply (g i))
  -- the germ of the pullback is the image of the germ under the stalk map
  have hgerm : ∀ i, (chartScheme N.chart).presheaf.germ ⊤
        (chartPoint B S hS Fs.1 N) trivial
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op).hom
          ((representedUnitSection B S hS T hT (g i)).eval (op (idChart B S hS T)))) =
      (((BigFppfOver.toScheme B S hS).map p).stalkMap (chartPoint B S hS Fs.1 N)).hom
        (((BigFppfOver.toScheme B S hS).obj T).presheaf.germ ⊤
          (((BigFppfOver.toScheme B S hS).map p) (chartPoint B S hS Fs.1 N)) trivial
          (g i)) := by
    intro i
    rw [heval i,
      Scheme.Hom.germ_stalkMap_apply ((BigFppfOver.toScheme B S hS).map p) ⊤
        (chartPoint B S hS Fs.1 N) trivial (g i)]
    rfl
  have hlist := congrArg List.ofFn (funext hgerm)
  have hreg' := (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular
    (chartLocalRing B S hS Fs.1 N)) hlist)).mpr hgreg
  exact ⟨fun i => representedUnitSection B S hS T hT (g i), hreg',
    (congrArg Ideal.ofList hlist).trans hgspan,
    forall_isRegular_etaleLocalRingMap_germ_of_isRegular_chartLocalRing B S hS ξ N
      (idChart B S hS T) p (hsq.trans (Category.comp_id _).symm) _ hreg'⟩

end AlgebraicGeometry.Space

end
