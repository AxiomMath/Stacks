module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData

/-!
# Effectivity and full faithfulness for quasi-coherent descent data

Stacks 023T asserts that for an fpqc covering family `f i : X i ⟶ S` every quasi-coherent descent
datum is effective and the canonical descent functor is fully faithful.  Both halves are
statements about the *full subcategories on quasi-coherent objects* of the pullback pseudofunctor
`AlgebraicGeometry.modulePullbackPseudofunctor` and of its categories of descent data, whereas
Mathlib's descent API — `CategoryTheory.Pseudofunctor.IsPrestack`,
`CategoryTheory.Pseudofunctor.IsStack`, `CategoryTheory.Pseudofunctor.IsPrestackFor` — speaks
about a pseudofunctor as a whole.  This file supplies the bridge across those two inclusions of
full subcategories, in both directions of 023T.

## Main results

* `CategoryTheory.Pseudofunctor.DescentData.objIso` of
  `StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves`, imported here: an
  isomorphism of descent data is an isomorphism in each
  component.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor`: the canonical descent functor
  on quasi-coherent modules is fully faithful as soon as the composite of the inclusion of the
  quasi-coherent modules with `CategoryTheory.Pseudofunctor.toDescentData` acts bijectively on
  morphisms.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful`: the same, from
  full faithfulness of `CategoryTheory.Pseudofunctor.toDescentData` on all sheaves of modules.
* `Stacks.Descent.isEffective_of_essImage`: a quasi-coherent descent datum is effective as soon
  as its underlying datum lies in the essential image of
  `CategoryTheory.Pseudofunctor.toDescentData` and quasi-coherence descends along the family.
* `Stacks.Descent.isEffective_of_essSurj`: the same with the essential-image hypothesis supplied
  by essential surjectivity.
* `Stacks.Descent.sieve_ofArrows_mem_fpqcTopology`: an fpqc covering family generates an fpqc
  covering sieve, which is the form in which the hypothesis of 023T feeds Mathlib's descent API.

## Implementation notes

The transfer of full faithfulness rests on
`AlgebraicGeometry.canonicalDescentFunctor_comp_ι`, which says that forgetting quasi-coherence
turns the canonical descent functor into `ι ⋙ toDescentData`.  Transporting full faithfulness
along that equality with `CategoryTheory.Functor.FullyFaithful.ofIso` and then descending it from
the composite with `CategoryTheory.Functor.FullyFaithful.ofCompFaithful` — the inclusion of a full
subcategory is faithful — gives the conclusion.

The hypotheses are phrased with the composite `ι ⋙ toDescentData`, never with the hom-sets
`M.obj ⟶ N.obj` of `AlgebraicGeometry.Scheme.Modules`.  This is not cosmetic: the source category
of `toDescentData` is the `CategoryTheory.Cat`-bundled category
`modulePullbackPseudofunctor.obj (.mk (op S))`, and identifying its `Category` instance with the
one on `SheafOfModules S.ringCatSheaf` forces the elaborator to unfold the whole pullback
adjunction, which does not terminate within the default heartbeat budget.  Inside a composite the
two categories are identified once, cheaply, at the level of types.

The transfer of effectivity needs one ingredient beyond the essential image: the module produced
on the base must itself be quasi-coherent.  That is not automatic, so it is a hypothesis — the
statement that quasi-coherence descends along the family.

## What 023T still needs

The hypotheses here are about quasi-coherent modules only, which is what 023T is about; the
`CategoryTheory.Pseudofunctor.IsPrestack` and `CategoryTheory.Pseudofunctor.IsStack` conditions
for `modulePullbackPseudofunctor` are the corresponding assertions for *arbitrary* sheaves of
modules, and are strictly stronger.  To obtain 023T itself one still has to prove, for an fpqc
covering family: the bijectivity hypothesis of
`nonempty_fullyFaithful_canonicalDescentFunctor` (descent of morphisms of quasi-coherent
sheaves), the essential-image hypothesis of `isEffective_of_essImage`, and the descent of
quasi-coherence.  The affine case of the underlying mathematics is
`Stacks.Descent.comonadicPullbackQcoh`; turning it into the single-morphism case of the
statements here additionally requires the comparison between
`CategoryTheory.Pseudofunctor.DescentData` and
`CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`, which is an open `TODO` of
`Mathlib/CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean`, and the globalization of
Stacks 023S to a general base needs the Zariski gluing of Stacks 023E.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite

universe t v' u' v₁ u₁ v u

namespace Stacks.Descent

section DescentData

variable {C : Type u₁} [Category.{v₁} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

end DescentData

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- An fpqc covering family generates an fpqc covering sieve.  This is the form in which the
hypothesis of Stacks 023T enters Mathlib's descent API, whose covering condition is membership of
the generated sieve in `AlgebraicGeometry.Scheme.fpqcTopology`. -/
theorem sieve_ofArrows_mem_fpqcTopology
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Sieve.ofArrows X f ∈ Scheme.fpqcTopology.{u} S :=
  Precoverage.generate_mem_toGrothendieck hfpqc

/-- **Full faithfulness of the canonical descent functor, reduced to descent of morphisms.**  If
pulling back morphisms along the family `f` is a bijection from morphisms of quasi-coherent
modules on `S` to morphisms of the associated descent data, then the canonical descent functor on
quasi-coherent modules is fully faithful.

This is the transfer of full faithfulness across the two inclusions of full subcategories: the
quasi-coherent modules inside all sheaves of modules, and the quasi-coherent descent data inside
all descent data. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor
    (h : ∀ M N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      Function.Bijective
        (((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
          modulePullbackPseudofunctor.toDescentData f).map : (M ⟶ N) → _)) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  ⟨(((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 h).some.ofIso
    (eqToIso (canonicalDescentFunctor_comp_ι f).symm)).ofCompFaithful⟩

/-- **Full faithfulness of the canonical descent functor, from the pseudofunctor.**  If
`CategoryTheory.Pseudofunctor.toDescentData` for the family `f` is fully faithful on all sheaves
of modules, then the canonical descent functor on quasi-coherent modules is fully faithful.

The hypothesis is Mathlib's `CategoryTheory.Pseudofunctor.IsPrestackFor` for the presieve
generated by `f`, by `CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff`.  It is strictly
stronger than what Stacks 023T asserts, since it is about arbitrary sheaves of modules. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful
    (h : (modulePullbackPseudofunctor.toDescentData f).FullyFaithful) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  nonempty_fullyFaithful_canonicalDescentFunctor fun _ _ ↦
    ((SheafOfModules.isQuasicoherent S.ringCatSheaf).fullyFaithfulι.comp h).map_bijective _ _

/-- **Effectivity of a quasi-coherent descent datum, reduced to the essential image.**  A
quasi-coherent descent datum is effective as soon as the underlying descent datum is isomorphic
to the one associated to some sheaf of modules on the base, and quasi-coherence descends along
the family.

The descent of quasi-coherence is a genuine extra hypothesis: the essential image of
`CategoryTheory.Pseudofunctor.toDescentData` produces a sheaf of modules on `S`, and it has to be
quasi-coherent before it is a witness for
`AlgebraicGeometry.QuasicoherentDescentData.IsEffective`. -/
theorem isEffective_of_essImage
    (hqc : ∀ M : S.Modules,
      (∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) → M.IsQuasicoherent)
    {D : QuasicoherentDescentData f}
    (hD : (modulePullbackPseudofunctor.toDescentData f).essImage D.obj) :
    D.IsEffective := by
  obtain ⟨M, ⟨e⟩⟩ := hD
  have hM : M.IsQuasicoherent := hqc M fun i ↦
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (X i).ringCatSheaf)
      (Pseudofunctor.DescentData.objIso e i).symm (D.property i)
  exact ⟨⟨M, hM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Effectivity of a quasi-coherent descent datum, from essential surjectivity.**  If
`CategoryTheory.Pseudofunctor.toDescentData` for the family `f` is essentially surjective and
quasi-coherence descends along `f`, then every quasi-coherent descent datum for `f` is
effective. -/
theorem isEffective_of_essSurj
    (hqc : ∀ M : S.Modules,
      (∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) → M.IsQuasicoherent)
    [(modulePullbackPseudofunctor.toDescentData f).EssSurj]
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  isEffective_of_essImage hqc (Functor.EssSurj.mem_essImage _ _)

end Stacks.Descent

end
