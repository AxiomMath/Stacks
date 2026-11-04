module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource

/-!
# Being at-worst-nodal of relative dimension one is étale local on the source

Let `f : X ⟶ S` be a morphism of schemes and let `{U i ⟶ X}` be an étale covering of its
source. This file proves that `f` is at-worst-nodal of relative dimension one if and only if
each composite `U i ⟶ X ⟶ S` is; in other words, being at-worst-nodal of relative dimension one
is étale local on the source.

## Main results

* `AlgebraicGeometry.syntomicOfRelativeDimension_one_of_forall_comp`: being syntomic of relative
  dimension one may be checked after an étale covering of the source.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_forall_comp`: the substantial
  direction, that being at-worst-nodal of relative dimension one may be checked after an étale
  covering of the source.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_of_mem_etalePrecoverage`: the
  resulting equivalence, for an étale covering presented as a covering presieve.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering`: **Stacks
  Project, Tag 0C5D** — the same equivalence for an étale covering presented as an indexed
  family.

## Implementation notes

An étale covering of `X` is membership of a presieve on `X` in
`AlgebraicGeometry.Scheme.etalePrecoverage`, which by
`AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff` is exactly a jointly surjective family
of étale morphisms to `X`. Being local on the source for that precoverage is
`CategoryTheory.MorphismProperty.IsLocalAtSource`, and the two halves of the definition of being
at-worst-nodal of relative dimension one are handled through it separately.

Being at-worst-nodal of relative dimension one is being syntomic of relative dimension one
together with unramifiedness over the base of the relative singular subscheme `Sing(f) ⊆ X`
(`AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`, the shape of condition (2) of
Tag 0C59). The source argues instead with the fibrewise condition (1) of that tag, reducing to a
base which is the spectrum of a field and quoting Tag 0C57 there; with the singular-subscheme
shape of the definition both halves descend directly, and no reduction to a field is needed.

Syntomicity is local on the source for the étale topology
(`AlgebraicGeometry.Syntomic.isLocalAtSource_etalePrecoverage`), which is the input Tag 0C5D
takes from Descent, Tags 036N and 036K; the clause on the local dimension of the fibres is the
content Tag 0C5D takes from Descent, Tag 04NL, and here it is
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_etale` applied to the étale morphism of fibres
`AlgebraicGeometry.fiberMapOfComp` induced by a member of the covering, exactly as in the
converse direction of Tag 0C5C.

For the singular subscheme the covering of `X` is pulled back to a covering of `Sing(f)`: the
member above `g : U ⟶ X` is `pullback.snd g Sing(f)ι`, which is étale as a base change of `g`,
and the family of these is jointly surjective because a point of a fibre product of schemes
exists above any pair of points with a common image
(`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`). The comparison
`AlgebraicGeometry.relativeSingularIdeal_comap_etale` identifies that fibre product with
`Sing(g ≫ f)` compatibly with the morphisms to `S`, through
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`. Unramifiedness is local on the source for the
étale topology (`AlgebraicGeometry.Unramified.isLocalAtSource_etalePrecoverage`), so the
hypothesis on the members of the covering gives it for `Sing(f) ⟶ S`.

## References

* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C5C](https://stacks.math.columbia.edu/tag/0C5C)
* [Stacks Project, Tag 0C5D](https://stacks.math.columbia.edu/tag/0C5D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Every member of an étale covering presieve is étale. -/
private theorem etale_of_mem_etalePrecoverage {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ Scheme.etalePrecoverage X) {U : Scheme.{u}} {g : U ⟶ X} (hg : R g) : Etale g :=
  hR.2 hg

/-- An étale covering presieve given by an indexed family is jointly surjective. -/
private theorem exists_mem_range_of_mem_etalePrecoverage {X : Scheme.{u}} {ι : Type*}
    {U : ι → Scheme.{u}} {k : ∀ i, U i ⟶ X}
    (hR : Presieve.ofArrows U k ∈ Scheme.etalePrecoverage X) (x : X) :
    ∃ i, x ∈ Set.range (k i).base :=
  ((Scheme.ofArrows_mem_precoverage_iff
    (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).mp hR).1 x

/-- Being syntomic of relative dimension one may be checked after an étale covering of the
source: syntomicity is local on the source for the étale topology, and an étale morphism of the
source induces an étale morphism of fibres, which preserves the local dimension of a fibre. -/
public theorem syntomicOfRelativeDimension_one_of_forall_comp {X S : Scheme.{u}} (f : X ⟶ S)
    {R : Presieve X} (hR : R ∈ Scheme.etalePrecoverage X)
    (h : ∀ ⦃U : Scheme.{u}⦄ ⦃g : U ⟶ X⦄, R g → SyntomicOfRelativeDimension 1 (g ≫ f)) :
    SyntomicOfRelativeDimension 1 f := by
  refine ⟨MorphismProperty.IsLocalAtSource.of_forall_comp (P := @Syntomic) hR
    fun _ _ hg => (h hg).1, fun x => ?_⟩
  obtain ⟨ι, U, k, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨i, y, hy⟩ := exists_mem_range_of_mem_etalePrecoverage hR x
  have : Etale (k i) := etale_of_mem_etalePrecoverage hR (Presieve.ofArrows.mk i)
  have hdim := (h (Presieve.ofArrows.mk i)).2 y
  have : Etale (fiberMapOfComp (k i) f ((k i ≫ f) y)) :=
    MorphismProperty.of_isPullback (isPullback_fiberMapOfComp (k i) f ((k i ≫ f) y)).flip
      inferInstance
  rw [topologicalKrullDimAt_eq_of_etale (fiberMapOfComp (k i) f ((k i ≫ f) y))
    ((k i ≫ f).asFiber y), fiberMapOfComp_asFiber (k i) f y] at hdim
  rw [← hy]
  exact hdim

/-- **The substantial half of Stacks Project, Tag 0C5D.** Being at-worst-nodal of relative
dimension one may be checked after an étale covering of the source.

Being syntomic of relative dimension one descends by
`AlgebraicGeometry.syntomicOfRelativeDimension_one_of_forall_comp`. For the relative singular
subscheme, the covering is pulled back along `Sing(f) ⟶ X`: its member above `g : U ⟶ X` is a
base change of `g`, hence étale, and the comparison
`AlgebraicGeometry.relativeSingularIdeal_comap_etale` identifies its source with
`Sing(g ≫ f)` compatibly with the morphisms to `S`, so unramifiedness over `S` of `Sing(f)`
follows because unramifiedness is local on the source for the étale topology. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_of_forall_comp {X S : Scheme.{u}} (f : X ⟶ S)
    {R : Presieve X} (hR : R ∈ Scheme.etalePrecoverage X)
    (h : ∀ ⦃U : Scheme.{u}⦄ ⦃g : U ⟶ X⦄, R g → IsAtWorstNodalOfRelativeDimensionOne (g ≫ f)) :
    IsAtWorstNodalOfRelativeDimensionOne f := by
  have hsyn : SyntomicOfRelativeDimension 1 f :=
    syntomicOfRelativeDimension_one_of_forall_comp f hR fun _ _ hg => (h hg).1
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn.1
  have : LocallyOfFiniteType f := inferInstance
  refine ⟨hsyn, ?_⟩
  obtain ⟨ι, U, k, rfl⟩ := R.exists_eq_ofArrows
  have hEt : ∀ i, Etale (k i) := fun i =>
    etale_of_mem_etalePrecoverage hR (Presieve.ofArrows.mk i)
  have hsnd : ∀ i, Etale (pullback.snd (k i) (relativeSingularIdeal f).subschemeι) := fun i =>
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (k i) (relativeSingularIdeal f).subschemeι) (hEt i)
  have hsurj : ∀ z : (relativeSingularIdeal f).subscheme, ∃ i,
      z ∈ Set.range (pullback.snd (k i) (relativeSingularIdeal f).subschemeι).base := fun z => by
    obtain ⟨i, y, hy⟩ := exists_mem_range_of_mem_etalePrecoverage hR
      ((relativeSingularIdeal f).subschemeι z)
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := k i)
      (g := (relativeSingularIdeal f).subschemeι) y z hy
    exact ⟨i, w, hw⟩
  have hcov : Presieve.ofArrows
      (fun i => pullback (k i) (relativeSingularIdeal f).subschemeι)
      (fun i => pullback.snd (k i) (relativeSingularIdeal f).subschemeι) ∈
        Scheme.etalePrecoverage (relativeSingularIdeal f).subscheme :=
    (Scheme.ofArrows_mem_precoverage_iff
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).mpr ⟨hsurj, hsnd⟩
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := @Unramified) hcov ?_
  rintro V p ⟨i⟩
  have : Etale (k i) := hEt i
  have hu : Unramified
      (((relativeSingularIdeal f).comap (k i)).subschemeι ≫ (k i ≫ f)) := by
    rw [relativeSingularIdeal_comap_etale f (k i)]
    exact (h (Presieve.ofArrows.mk i)).2
  have key : pullback.snd (k i) (relativeSingularIdeal f).subschemeι ≫
        (relativeSingularIdeal f).subschemeι ≫ f
      = ((relativeSingularIdeal f).comapIso (k i)).inv ≫
        ((relativeSingularIdeal f).comap (k i)).subschemeι ≫ (k i ≫ f) := by
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  rw [key]
  exact MorphismProperty.comp_mem _ _ _ (unramified_of_etale _) hu

/-- **Stacks Project, Tag 0C5D.** Let `f : X ⟶ S` be a morphism of schemes and let `R` be an
étale covering presieve of `X`. Then `f` is at-worst-nodal of relative dimension one if and only
if `g ≫ f` is at-worst-nodal of relative dimension one for every member `g` of `R`. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_iff_of_mem_etalePrecoverage
    {X S : Scheme.{u}} (f : X ⟶ S) {R : Presieve X} (hR : R ∈ Scheme.etalePrecoverage X) :
    IsAtWorstNodalOfRelativeDimensionOne f ↔
      ∀ ⦃U : Scheme.{u}⦄ ⦃g : U ⟶ X⦄, R g → IsAtWorstNodalOfRelativeDimensionOne (g ≫ f) := by
  refine ⟨fun hf _ g hg => ?_, isAtWorstNodalOfRelativeDimensionOne_of_forall_comp f hR⟩
  have : Etale g := etale_of_mem_etalePrecoverage hR hg
  exact isAtWorstNodalOfRelativeDimensionOne_comp_etale f g hf

/-- **Stacks Project, Tag 0C5D.** Let `f : X ⟶ S` be a morphism of schemes and let
`{U i ⟶ X}` be an étale covering. The following are equivalent:

1. `f` is at-worst-nodal of relative dimension one;
2. each `U i ⟶ S` is at-worst-nodal of relative dimension one.

In other words, being at-worst-nodal of relative dimension one is étale local on the source. -/
@[stacks 0C5D]
public theorem isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering {X S : Scheme.{u}}
    (f : X ⟶ S) {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ X)
    (hg : Presieve.ofArrows U g ∈ Scheme.etalePrecoverage X) :
    IsAtWorstNodalOfRelativeDimensionOne f ↔
      ∀ i, IsAtWorstNodalOfRelativeDimensionOne (g i ≫ f) :=
  (isAtWorstNodalOfRelativeDimensionOne_iff_of_mem_etalePrecoverage f hg).trans
    ⟨fun h i => h (Presieve.ofArrows.mk i), fun h _ _ hk => by
      obtain ⟨i⟩ := hk
      exact h i⟩

end AlgebraicGeometry

end
