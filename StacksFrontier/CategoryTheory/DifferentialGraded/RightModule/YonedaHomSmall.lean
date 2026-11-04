module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaHomCohomology

/-!
# Morphisms out of a representable are small, whatever the universe of the objects

Let `C` be a differential graded category whose objects lie in `Type u` and whose morphism
modules lie in `Type v`, with `u` and `v` unrelated. A homogeneous morphism of right differential
graded `C`-modules is a family indexed by the objects of `C`, so the morphism groups of
`K(Mod^dg(C))` live in `Type (max u v)` and are *not* `Type v`-small in general.

Morphisms **out of a representable** are. By the differential graded Yoneda lemma on homotopy
categories, `DGCategory.RightModule.homKEquivGradedCohomology`, the group
`Hom_{K(Mod^dg(C))}(h_X, M)` is the degree-zero cohomology `H^0(M X)` of the complex `M X`, and
that is a `Type v` by construction — `DGCategory.RightModule.gradedCohomology` is a quotient of
submodules of the values `M.obj X n`, which are objects of `Type v`. So the Hom group is
`Type v`-small even though the ambient category's morphism universe is `max u v`.

## Why this is the lever on the universe restriction of step 1 of [Stacks, Tag 09LK]

The reflector bridge
`CategoryTheory.ObjectProperty.exists_isTriangulated_reflector_localizingClosure`
asks for coproducts indexed by the *ambient morphism universe* and generators compact for those,
which for `K(Mod^dg(C))` means `Type (max u v)`-indexed coproducts. Only
`Type v`-indexed ones exist — `DGCategory.RightModule.hasCoproducts_rightModuleHomotopyCategory`
provides `HasCoproducts.{w}` on `rightModuleCategory.{w} C`, the degreewise direct sums, and
a `Type (max u v)`-indexed direct sum of `Type v`-valued modules has a `Type (max u v)`-valued
carrier, so it is not an object of the category at all. That mismatch is the whole of the condition
`u ≤ v` which every consumer of step 1 in this development carries.

The Bousfield construction behind the bridge, however, never forms a coproduct indexed by a
generic Hom group of the ambient: the families it sums are indexed by `Σ i, (G i ⟶ -)`, the
morphisms out of the *generators*. For representable generators this file says those index types
are `Type v`-small, so the construction stays inside the coproducts that do exist. Freeing the
index universe of the bridge and discharging the resulting smallness hypothesis with the instance
below is therefore a route to step 1 at `C : DGCategory.{v, u}` with `u` unrestricted, raising no
module value universe and so changing neither `D(Ab)` nor `D(E, d)`.

## The second demand, which this does not touch, and which is a genuine obstruction

The condition `u ≤ v` is imposed by *two* independent demands, and the above bears only on the
first. The second is the generating family of
`DGCategory.RightModule.yonedaInverseImage_eq_of_isTriangulated`: it must be indexed by a
nonempty `Type v` **and enumerate `Ac` up to isomorphism in `K(C)`** (its `hG`, consumed by
`DGCategory.RightModule.le_yonedaInverseImage`). The tautological enumeration used by
`DGCategory.RightModule.exists_chainEquivReflectorEvaluation_of_isTriangulated` is indexed by
`Subtype Ac`, a `Type u`. No smallness of Hom groups bears on this, and it is where the
remaining mathematics of [Stacks, Tag 09LK]'s step 1 sits.

*The form in the API is refutable.* Take `A = ModuleCat.{v} (ZMod 4)` and `C = Comp^dg(A)`.
Isomorphism in `K(C)` is homotopy equivalence, so `hG` asks the acyclic complexes to be
exhausted up to homotopy equivalence by a `Type v`-indexed family. For a cardinal `κ` the
2-periodic complex `(⋯ → ℤ/4 →^{·2} ℤ/4 →^{·2} ℤ/4 → ⋯)^{(κ)}` is acyclic — the image of
multiplication by `2` is `(2)`, which is also its kernel — and it is not contractible. The pair
`(dim_{ℤ/2}(M/2M), dim_{ℤ/2}(2M))` is a homotopy-equivalence invariant separating these as `κ`
ranges over `Cardinal.{v}`, which is not `Small.{v}`. So no such family exists.

*The thick-closure weakening is also false.* Asking instead that `Ac` be the **thick** closure of
a `Type v`-indexed family of its objects fails on the same example: a thick closure admits only
finite extensions and retracts, so it misses the `κ`-fold sum for infinite `κ`. The weakest
viable form is therefore the **localizing** one — that `Ac` be contained in the localizing
closure of a `Type v`-indexed set of acyclic objects.

*And even the localizing form does not plug in.* Discharging `Ac ≤ Φ⁻¹ N` from it needs
`Φ = (yonedaDGFunctor C).onK` to preserve infinite coproducts, and it does not:
`C(y, ⨁ᵢ Xᵢ) ≇ ⨁ᵢ C(y, Xᵢ)` in general, that failure being precisely the non-compactness of `y`.
No such preservation exists in this development — `YonedaSum.lean` proves only the module-side
`DGCategory.RightModule.bijective_cofanMap_coprodCofan`, the bijection for morphisms *out of a
representable* into a direct sum of modules, which is a different statement.

*This is not implied by [Stacks, Tag 09LK]'s own hypothesis.* Tag 09LK is stated over an
arbitrary abelian category, and its hypothesis is the everywhere-definedness of the
`D(Ab)`-valued `R Hom(K, -)`. That the acyclics of `K(A)` are generated by a set is
false-or-unknown at that generality — it is the well-generation difficulty for the localization
`K(A) ⥤ D(A)` — and nothing in the derivability hypothesis supplies it. So no hypothesis on `A`
is added anywhere here, and this demand is recorded rather than discharged.

## Main results

* `DGCategory.RightModule.small_hom_yonedaObjK`: `Hom_{K(Mod^dg(C))}(h_X, M)` is `Type v`-small,
  for every `X` and every `M`, with the universe of the objects of `C` unrestricted.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), step 1;
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the Yoneda lemma on cohomology.
-/

@[expose] public section

namespace DGCategory

universe v u r

open CategoryTheory

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

/-- **Morphisms out of a representable right differential graded module are small.** For `X` an
object of `C` and `M` an object of `K(Mod^dg(C))`, the group `Hom(h_X, M)` is `Type v`-small,
where `Type v` is the universe of the morphism modules of `C` — with no condition relating it to
the universe `Type u` of the objects of `C`.

The ambient morphism universe is `max u v`, a homogeneous morphism of modules being a family
indexed by the objects of `C`, so this is a genuine restriction of size and not a reindexing. It
holds because `DGCategory.RightModule.homKEquivGradedCohomology` identifies the group with
`DGCategory.RightModule.gradedCohomology M X 0`, which is a `Type v`. -/
instance small_hom_yonedaObjK (X : C.Obj) (M : (rightModuleCategory.{v} C).K) :
    Small.{v} (yonedaObjK X ⟶ M) :=
  small_of_injective (homKEquivGradedCohomology M X).injective

end RightModule

end DGCategory

end
