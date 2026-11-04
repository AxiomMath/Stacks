module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonRestriction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandBounded
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a locally bounded strictly perfect complex

Let `(C, O)` be a ringed site. Stacks 08JH identifies the derived internal Hom `RSheafHom(E, F)`
with the ordinary internal Hom complex `SheafHom(E, F)` when `E` is *strictly perfect*: bounded,
with every term a direct summand of a finite free `O`-module. In `AlgebraicGeometry.RingedSite`,
`strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand` weakens the termwise
half of that hypothesis to its local form. This file weakens the other half: the comparison

`Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)`

is an isomorphism as soon as `E` is strictly perfect **on the members of a family of objects
covering the final object** — no global bound on the degrees in which `E` is nonzero, and no
global splitting of its terms.

That is the hypothesis the geometry supplies. A perfect object of `D(𝒪_X)` whose Chern classes
are defined is represented, after pulling back along an envelope, by a complex of finite locally
free modules which is only *locally* bounded ([Stacks, Tag 0GUJ]); on a scheme that is not
quasi-compact no global bound exists, and a finite locally free module is not a global direct
summand of a finite free one.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_coversTop`: the internal Hom complex out of
  such an `E` carries a quasi-isomorphism of targets to a quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_coversTop`: **Stacks 08JH
  for a source that is strictly perfect only locally on the site.**

## Implementation notes

The descent is not a descent of the *comparison*, which would need invertibility in the derived
category to be local on the site — a statement that is false for a general morphism of `D(𝒪_X)`,
since a class in `H⁰(X, RSheafHom(K, L))` can vanish on a covering without vanishing. It is a
descent of the quasi-isomorphy that
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_iff` reduces the comparison to:
quasi-isomorphy of a morphism of complexes of sheaves of modules **is** local on the site, which
is `Stacks.SheafOfModules.quasiIso_of_coversTop`. So the whole content is the commuting square

`(SheafHom(E, F))|_V ⟶ (SheafHom(E, G))|_V`  versus  `SheafHom(E|_V, F|_V) ⟶ SheafHom(E|_V, G|_V)`,

which is `AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso_natural` at the identity of
`E` in the contravariant variable, together with
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand` on each member of the
covering.

The termwise hypothesis is stated as the **global** condition
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` on the slice over each member of the covering,
not as the local condition `IsLocallyFiniteFreeSummand` there. That is both the weaker
requirement at the point of use — the covering can always be refined until the terms are
genuinely split, which is how a finite locally free module is handled — and the one that avoids
the iterated slices `(C/V)/W` that the local condition on a slice quantifies over.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  Stacks.SheafOfModules.Tensor.ringSheaf

variable (X : RingedSite.{u, u, u})
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The strictly perfect case, locally on the site.** Let `V : ι → C` be a family of objects
covering the final object of the site and let `E` be a complex of `O`-modules whose restriction
to the slice over each `V i` has finitely many nonzero terms, each of them a direct summand of a
finite free `O|_{V i}`-module. Then the internal Hom complex out of `E` carries a
quasi-isomorphism of targets to a quasi-isomorphism.

Quasi-isomorphy is local on the site (`Stacks.SheafOfModules.quasiIso_of_coversTop`), the
restriction of `SheafHom(E, -)` to the slice over `V i` is `SheafHom(E|_{V i}, (-)|_{V i})` by
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso_natural`, and over `V i` the
hypothesis is the one of `homMap_quasiIso_of_isFiniteFreeSummand`. -/
theorem homMap_quasiIso_of_coversTop
    {F G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (f : F ⟶ G) [QuasiIso f]
    (E : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hbdd : ∀ i, {n : ℤ | ¬ IsZero ((restrictComplex X E (V i)).X n)}.Finite)
    (hterm : ∀ (i : ι) (n : ℤ),
      IsFiniteFreeSummand (X.over (V i)) ((restrictComplex X E (V i)).X n)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  refine Stacks.SheafOfModules.quasiIso_of_coversTop hV _ fun i => ?_
  have hfq : QuasiIso (((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) :=
    Stacks.SheafOfModules.quasiIso_overFunctor_mapHomologicalComplex_map (V i) f
  have hq : QuasiIso (homMap (X.over (V i))
      (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (𝟙 E))
      (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) := by
    rw [CategoryTheory.Functor.map_id]
    exact homMap_quasiIso_of_isFiniteFreeSummand (X.over (V i)) _ _ (hbdd i) (hterm i)
  have hnat := sheafHomRestrictionComplexIso_natural X (V i) (𝟙 E) f
  have key : ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homMap X (𝟙 E) f) =
        (sheafHomRestrictionComplexIso X (V i) E F).hom ≫
          homMap (X.over (V i))
            (((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (𝟙 E))
            (((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f) ≫
            (sheafHomRestrictionComplexIso X (V i) E G).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **Stacks 08JH for a source that is strictly perfect only locally on the site.** Let
`V : ι → C` be a family of objects covering the final object and let `E` be a complex of
`O`-modules whose restriction to the slice over each `V i` has finitely many nonzero terms, each
of them a direct summand of a finite free `O|_{V i}`-module. Then, for every target `F`, the
canonical comparison from the class of the internal Hom complex `SheafHom(E, F)` to the derived
internal Hom `RSheafHom(E, F)` is an isomorphism.

By `strictlyPerfectHomComparison_isIso_iff` this is the quasi-isomorphy of the map of internal
Hom complexes induced by the K-injective augmentation of `F`, which is
`homMap_quasiIso_of_coversTop`. Neither the global bound of
`strictlyPerfectHomComparison_isIso` nor the global splittings of its termwise hypothesis are
needed. -/
theorem strictlyPerfectHomComparison_isIso_of_coversTop
    (E F : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hbdd : ∀ i, {n : ℤ | ¬ IsZero ((restrictComplex X E (V i)).X n)}.Finite)
    (hterm : ∀ (i : ι) (n : ℤ),
      IsFiniteFreeSummand (X.over (V i)) ((restrictComplex X E (V i)).X n)) :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  (strictlyPerfectHomComparison_isIso_iff X D E F).2
    (homMap_quasiIso_of_coversTop X ((kInjectiveAugmentation X).app F) E hV hbdd hterm)

end AlgebraicGeometry.RingedSite

end
