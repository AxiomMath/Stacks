module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Restricting a morphism of derived categories along an arrow of a ringed site

Let `(C, O)` be a ringed site and let `g : W ⟶ V` be an arrow of `C`.  Restriction of sheaves of
modules to a slice is transitive on the nose: restricting to the slice over `V` and then along
`g` *is* restricting to the slice over `W`, as functors.  So the same holds for the functors
induced on unbounded derived categories, and a morphism `K|_V ⟶ L|_V` can be restricted to a
morphism `K|_W ⟶ L|_W`.

This file records that restriction operation.  It is the map that must appear on the
derived-category side of any statement that an identification of the sections of a complex with
a group of morphisms is compatible with restriction — for instance the naturality in the object
of the site of [Stacks, Tag 0A94].  That naturality **is** carried, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived`, as
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restrict`, with its
chain-level input in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturality`.  The
restriction map appearing there is stated at the derived-category objects of the *degreewise*
restrictions of two complexes, as
`AlgebraicGeometry.RingedSite.restrictDerivedSectionHom`, because that is the spelling
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom` lands in.  The
comparison of that spelling with `AlgebraicGeometry.RingedSite.restrictDerivedHom` below — a
conjugation by `CategoryTheory.Functor.mapDerivedCategoryFactors` of the restriction functors
themselves — is
`AlgebraicGeometry.RingedSite.restrictDerivedHom_restrictDerivedSectionHom`, in the file named
above.

## Main definitions

* `AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`: restriction to the slice over
  `V` followed by restriction along `g`, compared with restriction to the slice over `W`, on
  unbounded derived categories.
* `AlgebraicGeometry.RingedSite.restrictDerivedHom`: a morphism between the restrictions of two
  objects to the slice over `V`, restricted to the slice over `W`.

## Main results

* `AlgebraicGeometry.RingedSite.restrictDerivedHom_map`: restricting the restriction of a global
  morphism is its restriction; only the naturality of the comparison is involved.
* `AlgebraicGeometry.RingedSite.restrictDerivedHom_map_comp_map`: the same naturality used at the
  source and at the target at once — restrictions of morphisms over the whole site may be pulled
  out of the restriction map.

## Implementation notes

The composite `overFunctor V ⋙ overMap g` is definitionally `overFunctor W`, including the
additivity and exactness instances that `CategoryTheory.Functor.mapDerivedCategory` consumes.
That defeq is nevertheless **not** what
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso` is built on: the comparison
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` is composed with the derived action
of Mathlib's `SheafOfModules.overFunctorMap`, which is an honest natural isomorphism
`overFunctor V ⋙ overMap g ≅ overFunctor W`.

The reason is the same one recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IteratedSlice.lean`. The defeq
is affordable where both sides are *functors* — `overFunctor V ⋙ overMap g = overFunctor W` and
`(overFunctor V ⋙ overMap g).mapDerivedCategory = (overFunctor W).mapDerivedCategory` each hold
by `rfl` inside the default heartbeat budget. It is **not** affordable at any statement that
compares the two spellings at an *object* of the derived category, or compares two morphisms
between such objects: `eqToHom`-against-`𝟙` at that level costs upwards of half a million
heartbeats (a million unfoldings of `CategoryTheory.Functor.obj` through `sheafCompose` and
`PresheafOfModules.pushforward₀`) against a budget of two hundred thousand. So a definition that
leaves the identification implicit cannot be *computed with* afterwards: every consumer that
needs the value of `(overMapDerivedCategoryRestrictIso X g).inv.app (DerivedCategory.Q.obj K)`
would have to pay that defeq.

Composing with `mapDerivedCategoryIsoOfNatIso` of `SheafOfModules.overFunctorMap` moves the
identification into a term, where it is a morphism of complexes applied degreewise — and there,
being a morphism of sheaves of modules, it is cheap. The two values of the comparison at the
image of a complex are then computed, without any crossing, by
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso_inv_app_Q` and
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso_hom_app_Q` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived`.
Do not "simplify" the definition back to a bare
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and do not raise `maxHeartbeats`.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (X : RingedSite.{u, u, u})

/-- Abelian sheaves on a slice of the site have a sheafification, which is what makes the derived
category of modules on that slice available. -/
local instance hasSheafifyOver (V : X.C) : HasSheafify (X.J.over V) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat (X.J.over V)

/-- On a slice of the site the weak equivalences of abelian sheaves are the locally bijective
maps. -/
local instance wEqualsLocallyBijectiveOver (V : X.C) :
    (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (X.J.over V)

/-- Restriction of modules along an arrow of the site is additive, being a pushforward. -/
local instance additiveOverMap {V W : X.C} (g : W ⟶ V) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{u}
    ((Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).inv)).Additive

/-- Restriction of modules along an arrow of the site preserves finite limits. -/
local instance preservesFiniteLimitsOverMap {V W : X.C} (g : W ⟶ V) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction of modules along an arrow of the site preserves finite colimits. -/
local instance preservesFiniteColimitsOverMap {V W : X.C} (g : W ⟶ V) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- **Restriction to a slice is transitive on unbounded derived categories.** Restricting to the
slice over `V` and then along `g : W ⟶ V` is restricting to the slice over `W`.

It is the comparison of the derived action of a composite with the composite of the derived
actions, followed by the derived action of Mathlib's natural isomorphism
`SheafOfModules.overFunctorMap`; see the implementation notes for why that second step may not be
dropped even though the two composites of functors on sheaves of modules are definitionally
equal. -/
def overMapDerivedCategoryRestrictIso {V W : X.C} (g : W ⟶ V) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory ⋙
        (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (SheafOfModules.overFunctorMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)

/-- **Restricting a morphism between the restrictions of two objects.** A morphism
`K|_V ⟶ L|_V` in the derived category of modules on the slice over `V` is carried to a morphism
`K|_W ⟶ L|_W` by restricting it along `g` and reading the result through
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`.

This is the restriction map of the rule `V ↦ Hom(K|_V, L|_V)`. -/
def restrictDerivedHom {V W : X.C} (g : W ⟶ V)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj L) :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.obj K ⟶
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.obj L :=
  (overMapDerivedCategoryRestrictIso X g).inv.app K ≫
    (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.map φ ≫
      (overMapDerivedCategoryRestrictIso X g).hom.app L

/-- **Restricting the restriction of a global morphism is its restriction.** Only the naturality
of the comparison of restriction in one and in two steps is involved. -/
theorem restrictDerivedHom_map {V W : X.C} (g : W ⟶ V)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ψ : K ⟶ L) :
    restrictDerivedHom X g K L
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map ψ) =
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.map ψ := by
  rw [restrictDerivedHom, ← Functor.comp_map,
    (overMapDerivedCategoryRestrictIso X g).hom.naturality ψ, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

/-- **Restrictions of global morphisms may be pulled out of the restriction map.** A morphism
`K|_V ⟶ L|_V` of the form `α|_V ≫ χ ≫ β|_V`, with `α : K ⟶ K'` and `β : L' ⟶ L` morphisms over
the whole site and `χ : K'|_V ⟶ L'|_V`, restricts to `α|_W ≫ (χ restricted) ≫ β|_W`.

Like `AlgebraicGeometry.RingedSite.restrictDerivedHom_map` this is only the naturality of
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`, used now at the source and at
the target at once.  It is what reduces a restriction square stated at two chosen
*representatives* to the same square stated at the objects of `D(O)` they represent: the
comparison `AlgebraicGeometry.RingedSite.restrictModelIso` of a representative with the object it
represents is the restriction of a morphism over the whole site, composed with a comparison that
does not mention the object of the site at all. -/
theorem restrictDerivedHom_map_comp_map {V W : X.C} (g : W ⟶ V)
    (K K' L L' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (α : K ⟶ K') (β : L' ⟶ L)
    (χ : (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj K' ⟶
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj L') :
    restrictDerivedHom X g K L
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map α ≫ χ ≫
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map β) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.map α ≫
        restrictDerivedHom X g K' L' χ ≫
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategory.map β := by
  rw [restrictDerivedHom, restrictDerivedHom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.comp_map _
      (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory α,
    ← Functor.comp_map _
      (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory β,
    reassoc_of% ((overMapDerivedCategoryRestrictIso X g).inv.naturality α),
    (overMapDerivedCategoryRestrictIso X g).hom.naturality β, Functor.comp_map]

end AlgebraicGeometry.RingedSite

end
