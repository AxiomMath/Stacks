module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor

/-! # The internal Hom bifunctor on a ringed site with unequal universes

`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor` is stated for a
`AlgebraicGeometry.RingedSite.{u, u, u}` and complexes of `SheafOfModules.{u}`. The three site
universes are collapsed there onto the module universe because the internal Hom complex of
Stacks 0A8X raises the module universe: for `X : RingedSite.{u, v, w}` and complexes of
`SheafOfModules.{m}`, the complex `(sheafHomComplex X L M).obj` is a complex of
`SheafOfModules.{max u v m}`, so the construction is an endo-operation only when
`max u v m = m`.

That is an equation between the *module* universe and the site universes, not between the site
universes with each other. This file states the bifunctor under exactly that equation, in the
only form Lean can express it: the module universe is written as `max u v m`, for which
`max u v (max u v m) = max u v m` holds by normalisation of universe levels. No hypothesis on
the site is needed and no new mathematics is involved — the two ingredients,
`AlgebraicGeometry.RingedSite.homMap_id` and `AlgebraicGeometry.RingedSite.homMap` itself, are
already stated at `RingedSite.{u, v, w}` with modules in `m`, and so now are the composition
law `AlgebraicGeometry.RingedSite.homMap_comp` and the cochain-level
`AlgebraicGeometry.RingedSite.cochainConj_comp` beneath it — composition of `homMap`s needs no
absorption at all, since both sides already live in `max u v m`, so `Bifunctor.lean` states them
in that generality and this file no longer restates them.

What this file does is assemble the bifunctor at the absorbing module universe `max u v m`.

The point is the small étale ringed site, which is a `RingedSite.{u + 1, u, u}`. There
`max (u + 1) u m = m` has the solution `m = u + 1`, so
`AlgebraicGeometry.RingedSite.Raised.sheafHomComplexBifunctor` is available on it for complexes
of `SheafOfModules.{u + 1}`, whereas
`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor` is available on it for no module
universe whatsoever: its argument would have to be a `RingedSite.{u + 1, u + 1, u + 1}`.

## Main definitions

* `AlgebraicGeometry.RingedSite.Raised.sheafHomComplexBifunctor`: the internal Hom complex of
  complexes of `SheafOfModules.{max u v m}` on a `RingedSite.{u, v, w}`, as a bifunctor,
  contravariant in its source.

## Main results

* `AlgebraicGeometry.RingedSite.Raised.sheafHomComplexBifunctor_eq`: at
  `RingedSite.{u, u, u}` and module universe `u` this bifunctor *is*
  `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`, so the generalisation names the same
  object and not a parallel one.

## Implementation notes

The declarations live in the namespace `AlgebraicGeometry.RingedSite.Raised` rather than in
`AlgebraicGeometry.RingedSite`, because each of them generalises a declaration of that namespace
which keeps its name and its statement. `sheafHomComplexBifunctor_eq` is the bridge between the
two spellings, and it is `rfl`: the definition below is the definition of `Bifunctor.lean` with
the universes freed, so at the collapsed universes the two are the same term.

## References

* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m t u v w

namespace AlgebraicGeometry.RingedSite.Raised

variable (X : RingedSite.{u, v, w})

/-! ### The composition laws at unequal universes

They are no longer restated here: `AlgebraicGeometry.RingedSite.cochainConj_comp` and
`AlgebraicGeometry.RingedSite.homMap_comp` of `InternalHom/Bifunctor.lean` are themselves
stated at `RingedSite.{u, v, w}` with an arbitrary module universe, which is what this
section used to duplicate. -/

/-! ### The bifunctor at an absorbing module universe -/

/-- **The internal Hom complex of complexes of `O`-modules on a ringed site whose three
universes are unrelated, as a bifunctor**, contravariant in its source and covariant in its
target.

The module universe is `max u v m`, which is the general solution of the equation
`max u v ? = ?` that makes the internal Hom complex of Stacks 0A8X an endo-operation. For a
`RingedSite.{u, u, u}` and `m = u` this is
`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`
(`AlgebraicGeometry.RingedSite.Raised.sheafHomComplexBifunctor_eq`); for the small étale ringed
site of a scheme, a `RingedSite.{u + 1, u, u}`, it is the bifunctor on complexes of
`SheafOfModules.{u + 1}`, which the collapsed statement provides for no module universe at
all. -/
def sheafHomComplexBifunctor :
    (CochainComplex (SheafOfModules.{max u v m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{max u v m}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v m}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ where
  obj K :=
    { obj := fun M => (sheafHomComplex X K.unop M).obj
      map := fun m => homMap X (𝟙 K.unop) m
      map_id := fun M => homMap_id X K.unop M
      map_comp := fun m m' => by rw [homMap_comp, Category.comp_id] }
  map k :=
    { app := fun M => homMap X k.unop (𝟙 M)
      naturality := fun M M' m => by
        change homMap X (𝟙 _) m ≫ homMap X k.unop (𝟙 M') =
          homMap X k.unop (𝟙 M) ≫ homMap X (𝟙 _) m
        rw [homMap_comp, homMap_comp, Category.comp_id, Category.id_comp, Category.comp_id,
          Category.id_comp] }
  map_id K := NatTrans.ext (funext fun M => homMap_id X K.unop M)
  map_comp k k' := NatTrans.ext (funext fun M => by
    change homMap X (k'.unop ≫ k.unop) (𝟙 M) =
      homMap X k.unop (𝟙 M) ≫ homMap X k'.unop (𝟙 M)
    rw [homMap_comp, Category.comp_id])

/-- The internal Hom bifunctor has the internal Hom complexes as its values. -/
lemma sheafHomComplexBifunctor_obj_obj
    (K M : CochainComplex (SheafOfModules.{max u v m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor.{m, u, v, w} X).obj (op K)).obj M =
      (sheafHomComplex X K M).obj := rfl

/-- The internal Hom bifunctor acts on a morphism of targets by postcomposition. -/
lemma sheafHomComplexBifunctor_obj_map
    (K : CochainComplex (SheafOfModules.{max u v m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {M M' : CochainComplex (SheafOfModules.{max u v m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (m : M ⟶ M') :
    ((sheafHomComplexBifunctor.{m, u, v, w} X).obj (op K)).map m = homMap X (𝟙 K) m := rfl

/-- The internal Hom bifunctor acts on a morphism of sources by precomposition. -/
lemma sheafHomComplexBifunctor_map_app
    {K K' : CochainComplex (SheafOfModules.{max u v m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (k : K' ⟶ K)
    (M : CochainComplex (SheafOfModules.{max u v m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor.{m, u, v, w} X).map (op k)).app M = homMap X k (𝟙 M) := rfl

/-! ### Agreement with the collapsed statement -/

/-- **The generalisation names the same bifunctor.** On a ringed site whose three universes
coincide, and at the module universe equal to them,
`AlgebraicGeometry.RingedSite.Raised.sheafHomComplexBifunctor` is
`AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`.

Nothing has been weakened or replaced: the definition above is the definition of
`Bifunctor.lean` read with the universes freed, so at the collapsed universes the two are the
same term. -/
theorem sheafHomComplexBifunctor_eq (Y : RingedSite.{u, u, u}) :
    sheafHomComplexBifunctor.{u, u, u, u} Y =
      AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor Y :=
  rfl

end AlgebraicGeometry.RingedSite.Raised

end
