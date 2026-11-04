module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceTransitivity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness descends along a covering family of a small étale site

Let `B` be a big étale site, `S` a scheme in it and `{E i}` a family of objects of the small
étale site of `S` whose structure morphisms cover `S`. A morphism `f : U ⟶ S` of schemes is
finite exactly when each of its base changes along those structure morphisms is finite.

Nothing new about finiteness is proved here. Finiteness is local on the base for the fpqc
topology — `Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc`, Stacks Tag 02LA — and the
structure morphisms of a covering family of the small étale site are an fpqc covering family
of `S`, since they are étale, hence flat and locally of finite presentation, and jointly
surjective: that is
`AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`. What is added
is the combination of the two, in the shape that a descent problem on the small étale site
produces: the index type of the family is arbitrary — covering families of the small étale site
of a `BigEtaleSite.{u}` are indexed by `Type (u + 1)` — and the base changes are presented by
given cartesian squares rather than by chosen fibre products.

## Main results

* `AlgebraicGeometry.SmallEtale.isFinite_iff_forall_of_coversTop` — the equivalence, for base
  changes presented by cartesian squares.
* `AlgebraicGeometry.SmallEtale.isFinite_of_coversTop` — the direction that descends
  finiteness.
* `AlgebraicGeometry.SmallEtale.isFinite_structureMorphism_of_coversTop` — the same, for the
  structure morphism of an object of the small étale site and its small étale base changes.

## References

* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finiteness is local on the base for a covering family of the small étale site.** Let
`{E i}` be a family of objects of the small étale site of `S` whose sieve of objects covers the
final object, let `f : U ⟶ S` be a morphism of schemes, and present the base change of `f` along
the structure morphism of `E i` by a cartesian square with sides `q i`, `f' i`, `f` and that
structure morphism. Then `f` is finite if and only if every `f' i` is.

The family is an fpqc covering of `S` and finiteness is fpqc local on the base, Stacks Tag
02LA. -/
@[ega "IV 2.7.1" "(xv), special case"]
public theorem isFinite_iff_forall_of_coversTop {I : Type w} (E : I → SmallEtale B S hS)
    (hE : (SmallEtale.topology B S hS).CoversTop E) {U : Scheme.{u}} (f : U ⟶ S)
    {U' : I → Scheme.{u}} {q : ∀ i, U' i ⟶ U}
    {f' : ∀ i, U' i ⟶ (SmallEtale.toScheme B S hS).obj (E i)}
    (hsq : ∀ i, IsPullback (q i) (f' i) f (B.inclusion.map (E i).obj.hom)) :
    IsFinite f ↔ ∀ i, IsFinite (f' i) := by
  have _hloc := Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc.{u}
  have _hri : MorphismProperty.RespectsIso (@IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    _hloc.toRespects
  have hiff : ∀ i, IsFinite (pullback.snd f (B.inclusion.map (E i).obj.hom)) ↔
      IsFinite (f' i) := by
    intro i
    have _hp := (hsq i).hasPullback
    rw [← (hsq i).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso
        (P := (@IsFinite.{u} : MorphismProperty Scheme.{u}))]
  rw [MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := (@IsFinite.{u} : MorphismProperty Scheme.{u})) (K := Scheme.fpqcPrecoverage.{u})
    (presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS E hE) (f := f)]
  refine ⟨fun h i ↦ (hiff i).1 (h _ ⟨i⟩), fun h V g hgp hg ↦ ?_⟩
  obtain ⟨i⟩ := hg
  exact (hiff i).2 (h i)

/-- **Finiteness descends along a covering family of the small étale site.** The direction of
`AlgebraicGeometry.SmallEtale.isFinite_iff_forall_of_coversTop` that produces finiteness of
`f : U ⟶ S` from finiteness of its base changes. -/
public theorem isFinite_of_coversTop {I : Type w} (E : I → SmallEtale B S hS)
    (hE : (SmallEtale.topology B S hS).CoversTop E) {U : Scheme.{u}} (f : U ⟶ S)
    {U' : I → Scheme.{u}} {q : ∀ i, U' i ⟶ U}
    {f' : ∀ i, U' i ⟶ (SmallEtale.toScheme B S hS).obj (E i)}
    (hsq : ∀ i, IsPullback (q i) (f' i) f (B.inclusion.map (E i).obj.hom))
    (hfin : ∀ i, IsFinite (f' i)) :
    IsFinite f :=
  (isFinite_iff_forall_of_coversTop B S hS E hE f hsq).2 hfin

/-- **Finiteness of the structure morphism of an object of the small étale site descends along a
covering family.** If the small étale base change of `U` along every member of a covering family
of the small étale site of `S` has finite structure morphism, then so does `U`.

The base changes are fibre products of schemes by
`AlgebraicGeometry.isPullback_smallEtaleBaseChange`, so this is
`AlgebraicGeometry.SmallEtale.isFinite_of_coversTop` at those squares. -/
public theorem isFinite_structureMorphism_of_coversTop {I : Type w} (E : I → SmallEtale B S hS)
    (hE : (SmallEtale.topology B S hS).CoversTop E) (U : SmallEtale B S hS)
    (hfin : ∀ i, IsFinite (B.inclusion.map
      (((smallEtaleBaseChange B (E i).obj.hom).obj U).obj.hom))) :
    IsFinite (B.inclusion.map U.obj.hom) :=
  isFinite_of_coversTop B S hS E hE _
    (fun i ↦ isPullback_smallEtaleBaseChange B (E i).obj.hom U) hfin

end AlgebraicGeometry.SmallEtale

end
