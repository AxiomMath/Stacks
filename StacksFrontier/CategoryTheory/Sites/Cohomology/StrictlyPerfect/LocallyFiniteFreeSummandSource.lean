module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom complex out of a locally finite free single term

Let `(C, O)` be a ringed site, let `A` be a sheaf of `O`-modules which is *locally* a direct
summand of a finite free module — that is, there is a family of objects covering the final
object of the site on each member of which the restriction of `A` is a retract of `O^{⊕r}` —
and let `A[k]` be `A` placed in a single degree `k`. Then

`SheafHom(A[k], F) ⟶ SheafHom(A[k], G)`

is a quasi-isomorphism whenever `F ⟶ G` is one.

For a *globally* finite free summand this is
`AlgebraicGeometry.RingedSite.homMap_single_quasiIso_of_isFiniteFreeSummand`, the single-degree
base case of Stacks 08JH. The global hypothesis is however strictly stronger than what the
geometry supplies: an invertible sheaf of modules, or more generally a finite locally free
sheaf, is only locally a direct summand of a finite free module and in general is not one
globally — on `P^1` there is no nonzero morphism `O(1) ⟶ O^{⊕n}` at all, so `O(1)` is not a
retract of any finite free module. Every source which is finite locally free therefore needs
the local hypothesis.

The proof is a descent with two inputs. Quasi-isomorphy of a morphism of complexes of sheaves
of modules is local on the site (`Stacks.SheafOfModules.quasiIso_of_coversTop`), and the
internal Hom complex commutes with restriction to a slice compatibly with the induced maps
(`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` and its naturality, the
chain-level form of Stacks 08JB). Over a member `V` of the covering family the restriction of
`A[k]` is `A|_V` placed in degree `k`, which is a finite free summand there, and the restriction
of `F ⟶ G` is still a quasi-isomorphism because restriction is exact; so the global lemma
applies over `V`.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsLocallyFiniteFreeSummand`: a sheaf of `O`-modules is locally a
  direct summand of a finite free module.

## Main results

* `AlgebraicGeometry.RingedSite.restrictSingleIso`: the restriction to a slice of a complex
  concentrated in one degree is the restriction of its term, in that degree.
* `AlgebraicGeometry.RingedSite.homMap_single_quasiIso_of_isLocallyFiniteFreeSummand`: **the
  single-degree case for a source which is only locally a direct summand of a finite free
  module.**

## Implementation notes

The predicate indexes its covering family by a type in the universe of the objects of the site.
That is the universe in which the covering families attached to an invertible sheaf of modules
already live (`Stacks.SheafOfModules.InvertibleSummandIndex`), and
`CategoryTheory.GrothendieckTopology.CoversTop` places no constraint on the index type, so
nothing is lost.

`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` is used rather than the predicate
`IsStrictlyPerfect` carrying the Stacks 08FL tag, because that predicate is universe-monomorphic
in the ring and module universes and cannot be mentioned at `RingedSite.{u, u, u}`.

Sheaves of modules on the slice over `V` are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O` in
`AlgebraicGeometry.RingedSite.sheafHomComplex` and by
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V` in
`AlgebraicGeometry.RingedSite.restrictComplex`; the two agree, and the local
`implicit_reducible` attributes below are what lets the elaborator see it, exactly as for
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.pushforward
  SheafOfModules.overFunctor

variable (X : RingedSite.{u, u, u})

/-- **A sheaf of modules locally a direct summand of a finite free module**: there is a family
of objects covering the final object of the site on each member of which the restriction of `M`
is a retract of a finite free `O`-module.

This is the local form of `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`, which asks for a
retraction over the whole site, and the ringed-site form of
`Stacks.SheafOfModules.IsLocallyFiniteFreeSummand`, which says the same thing for a ringed space
in terms of open neighbourhoods of points. -/
@[sga "6 II 2.0" "special case"]
def IsLocallyFiniteFreeSummand
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∃ (ι : Type u) (V : ι → X.C), X.J.CoversTop V ∧
    ∀ i, IsFiniteFreeSummand (X.over (V i)) (M.over (V i))

/-- The restriction to the slice over `V` of a complex concentrated in degree `k` is the
restriction of its degree-`k` term, placed in degree `k`: restriction is additive and preserves
zero morphisms, so it commutes with placing a module in a single degree. -/
def restrictSingleIso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : X.C) (k : ℤ) :
    restrictComplex X ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj M) V ≅
      (HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
        (ComplexShape.up ℤ) k).obj (M.over V) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (ComplexShape.up ℤ) k).app M

/-- **The single-degree case for a source which is only locally a direct summand of a finite
free module.** If `A` is locally a direct summand of a finite free `O`-module and `f : F ⟶ G` is
a quasi-isomorphism, then the induced map of internal Hom complexes out of `A` placed in degree
`k` is a quasi-isomorphism.

Quasi-isomorphy is local on the site, and over a member of a covering family trivializing `A`
the statement is `homMap_single_quasiIso_of_isFiniteFreeSummand` for the restricted data,
transported along the chain-level restriction isomorphism of the internal Hom complex. -/
theorem homMap_single_quasiIso_of_isLocallyFiniteFreeSummand
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) [QuasiIso f] (k : ℤ)
    {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hA : IsLocallyFiniteFreeSummand X A) :
    QuasiIso (homMap X
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj A)) f) := by
  obtain ⟨ι, V, hV, hloc⟩ := hA
  set E := (HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) k).obj A with hE
  refine Stacks.SheafOfModules.quasiIso_of_coversTop hV (homMap X (𝟙 E) f) fun i => ?_
  have hres : QuasiIso (restrictComplexMap X (V i) f) := by
    have : (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).PreservesHomology :=
      Stacks.SheafOfModules.preservesHomology_overFunctor (V i)
    infer_instance
  have hfree : QuasiIso (homMap (X.over (V i))
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)))
        (ComplexShape.up ℤ) k).obj (A.over (V i)))) (restrictComplexMap X (V i) f)) :=
    @homMap_single_quasiIso_of_isFiniteFreeSummand (X.over (V i)) _ _
      (restrictComplexMap X (V i) f) hres k _ (hloc i)
  have hrestr : QuasiIso (homMap (X.over (V i)) (𝟙 (restrictComplex X E (V i)))
      (restrictComplexMap X (V i) f)) :=
    @homMap_quasiIso_of_retract (X.over (V i)) _ _ _ _
      { i := (restrictSingleIso X A (V i) k).hom
        r := (restrictSingleIso X A (V i) k).inv
        retract := (restrictSingleIso X A (V i) k).hom_inv_id }
      (restrictComplexMap X (V i) f) hfree
  have hid : restrictComplexMap X (V i) (𝟙 E) = 𝟙 (restrictComplex X E (V i)) :=
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_id E
  have heq : restrictComplexMap X (V i) (homMap X (𝟙 E) f)
      = ((sheafHomRestrictionComplexIso X (V i) E F).hom ≫
          homMap (X.over (V i)) (restrictComplexMap X (V i) (𝟙 E))
            (restrictComplexMap X (V i) f)) ≫
        (sheafHomRestrictionComplexIso X (V i) E G).inv :=
    (Iso.eq_comp_inv _).2 (sheafHomRestrictionComplexIso_natural X (V i) (𝟙 E) f)
  change QuasiIso (restrictComplexMap X (V i) (homMap X (𝟙 E) f))
  rw [heq, hid]
  exact quasiIso_comp _ _
    (hφ := quasiIso_comp _ _
      (hφ := @quasiIso_of_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _) _ _)
      (hφ' := hrestr))
    (hφ' := @quasiIso_of_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv _) _ _)

end AlgebraicGeometry.RingedSite

end
