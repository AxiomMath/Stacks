module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature

/-!
# Perfectness along a functor with an exact localization square

Let `(C, O)` and `(D, O')` be ringed sites, let `u : D ⥤ C` be a continuous functor whose image
covers the final object of `Sh(C)`, and let `F : Mod(O') ⥤ Mod(O)` be an additive functor.
Suppose that for every object `W` of `D` there is an exact additive
`F_W : Mod(O'|_W) ⥤ Mod(O|_{u(W)})` carrying the unit to the unit, together with a
*localization square*

```
  (- |_W) ⋙ F_W  ≅  F ⋙ (- |_{u(W)}) .
```

Then `F` carries a perfect complex of `O'`-modules to a perfect complex of `O`-modules,
degreewise, and — when `F` is itself exact — a perfect object of `D(O')` to a perfect object of
`D(O)`.

This is the perfectness counterpart of the pseudo-coherence transfer in
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/`,
file `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/PseudoCoherenceAlongAnExactFunctor.lean`, and it exists for the same reason: the only
perfectness-preservation statement in this
development, Stacks 08H6
(`AlgebraicGeometry.RingedSite.Hom.isPerfect_derivedPullback`), is stated for an
`AlgebraicGeometry.RingedSite.Hom` between two `AlgebraicGeometry.RingedSite.{0, 0, 0}`, and
neither constraint is satisfiable by the comparison `ε` of Stacks 08H7: `RingedSite.Hom` requires
the objects and the morphisms of both sites to share one universe, whereas the small étale site
of a scheme over `Scheme.{u}` is a `RingedSite.{u + 1, u, u}`.

## Why the square is a hypothesis and not derivable

`AlgebraicGeometry.RingedSite.IsPerfectComplex` quantifies over the objects of the site and asks
for a strictly perfect complex on the *slice* over each member of a covering.  So the hypothesis
is a family of complexes on the slices of `D` and the conclusion a family of complexes on the
slices of `C`, and a functor `Mod(O') ⥤ Mod(O)` does not act on slice categories at all: without
`F_W` and the square there is nothing to apply to the given local model.  The square is
irreducible input, exactly as in the pseudo-coherent case.

## What is *not* needed

Nothing here mentions a morphism of ringed topoi, a derived pullback, or a K-flat resolution; and
nothing here passes through Stacks 08G6, whose available form
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect` rests on
Stacks 08FR and is therefore confined to a site whose objects and morphisms share a universe.
The definition of `IsPerfectComplex` is used directly, through
`AlgebraicGeometry.RingedSite.isPerfectComplex_iff`.

* Strict perfectness is carried by `SheafOfModules.isStrictlyPerfect_map` at independent object
  and morphism universes, so neither `F` nor `F_W` has to be a pullback along a morphism of
  ringed topoi.
* The quasi-isomorphism is carried because `F_W` is exact: an exact additive functor preserves
  homology, hence `CategoryTheory.QuasiIso`
  (`HomologicalComplex.quasiIso_map_of_preservesHomology`), and composing with an isomorphism of
  complexes preserves it too.  This replaces the two separate cohomological conditions that the
  pseudo-coherent transfer has to move, and it is the only difference between the two arguments.
* The covering is carried by `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype`, which is
  stated at independent object and morphism universes, so no smallness is imposed on either site.

Consequently the statement holds with the two sites' object and morphism universes independent,
sharing only the universe `w` of the sections of the two structure sheaves — the shape in which
the comparison `ε` of Stacks 08H7 lives.

## Main results

* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectQuasiIso_of_hom`: a strictly perfect local model
  over an object descends along an arrow into it.
* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectQuasiIso_map`: the square carries a local model
  over `W` to one over `u(W)`.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_mapHomologicalComplex`: the transfer of
  perfectness of complexes.
* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory` and
  `.isPerfect_mapDerivedCategory_of_hypotheses`: the same transfer in the derived category, for
  `F` exact.

## Implementation notes

The square read on cochain complexes is `AlgebraicGeometry.RingedSite.squareComplexIso`, already
used for the pseudo-coherent transfer; it is reused rather than restated, the two transfers
needing the very same comparison.

`AlgebraicGeometry.RingedSite.HasStrictlyPerfectModel` is taken: it is a `private` definition of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DerivedPullbackAlongRingedTopoi.lean`, where
it carries a *derived-category* isomorphism rather than a chain-level quasi-isomorphism and is
pinned to `SheafOfModules.{0}`.  The predicate here is therefore named
`HasStrictlyPerfectQuasiIso`, after the datum it holds.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

/-! ### Strictly perfect local models over one object -/

section Model

variable (X : RingedSite.{uX, vX, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] overMapLimits overMapColimits

/-- The datum that `AlgebraicGeometry.RingedSite.IsPerfectComplex` asks for over one object `V` of
the site: a strictly perfect complex on the slice over `V` and a quasi-isomorphism from it to
`K|_V`.  This is the body of that definition, named so that the two halves of the transfer below
can be stated separately. -/
def HasStrictlyPerfectQuasiIso
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      ∃ q : P ⟶ X.restrictComplex K V, QuasiIso q

/-- Perfectness of a complex is: every object has a covering all of whose members carry a strictly
perfect local model.  This holds by definition, and is stated so that the two quantifiers are
visible. -/
theorem isPerfectComplex_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    X.IsPerfectComplex K ↔
      ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
        ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → X.HasStrictlyPerfectQuasiIso K V :=
  Iff.rfl

/-- **A strictly perfect local model descends along an arrow of the site.**  Restriction to a
smaller slice is exact and carries the unit to the unit, so it preserves strict perfectness
(`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`) and the
quasi-isomorphism, and it carries the restriction of the ambient complex to the smaller
restriction (`Stacks.SheafOfModules.overFunctorMapComplexIso`).

This is what makes a covering whose arrows have arbitrary sources usable. -/
theorem hasStrictlyPerfectQuasiIso_of_hom
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {U V : X.C} (g : V ⟶ U)
    (h : X.HasStrictlyPerfectQuasiIso K U) : X.HasStrictlyPerfectQuasiIso K V := by
  obtain ⟨P, hP, q, hq⟩ := h
  exact ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    ((SheafOfModules.overMap.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q ≫
    ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K).hom, inferInstance⟩

end Model

/-! ### The transfer -/

section Transfer

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (u : Y.C ⥤ X.C)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [hFadd : F.Additive]
  (G : ∀ W : Y.C, SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⥤
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))

/-- **The image of a strictly perfect local model is one over the image object.**  Apply `F_W`
degreewise: strict perfectness is preserved because `F_W` is additive, preserves finite colimits
and carries the unit to the unit; the quasi-isomorphism is preserved because `F_W` is exact, hence
preserves homology; and the target is identified with `(F K)|_{u(W)}` by the localization square,
read on complexes as `AlgebraicGeometry.RingedSite.squareComplexIso`. -/
theorem hasStrictlyPerfectQuasiIso_map (W : Y.C) [(G W).Additive]
    [PreservesFiniteLimits (G W)] [PreservesFiniteColimits (G W)]
    (ηG : (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (h : Y.HasStrictlyPerfectQuasiIso K W) :
    X.HasStrictlyPerfectQuasiIso
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (u.obj W) := by
  obtain ⟨P, hP, q, hq⟩ := h
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w} (G W) ηG hP,
    ((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫
      ((squareComplexIso u F G W sq).app K).hom, inferInstance⟩

/-- **Perfectness of complexes transfers along an additive functor with an exact localization
square.**  If `K` is a perfect complex of `O'`-modules then the degreewise image `F K` is a
perfect complex of `O`-modules.

The covering of an object `U` of `C` that the conclusion asks for is the sieve of arrows factoring
through some `u(W)` with `W` carrying a strictly perfect local model of `K|_W`; it is covering by
`CategoryTheory.GrothendieckTopology.coversTop_obj_subtype`, which refines the given covering of
the final object by the `u(W)` to those `W`.  Over such a `u(W)` the model is carried across by
`F_W` (`hasStrictlyPerfectQuasiIso_map`), and along an arrow `V ⟶ u(W)` it descends
(`hasStrictlyPerfectQuasiIso_of_hom`), which is what the arrows of that covering supply. -/
theorem isPerfectComplex_mapHomologicalComplex [hu : u.IsContinuous Y.J X.J]
    (hTop : X.J.CoversTop u.obj)
    [hGadd : ∀ W : Y.C, (G W).Additive]
    [hGlim : ∀ W : Y.C, PreservesFiniteLimits (G W)]
    [hGcolim : ∀ W : Y.C, PreservesFiniteColimits (G W)]
    (ηG : ∀ W : Y.C,
      (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : ∀ W : Y.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Y.IsPerfectComplex K) :
    X.IsPerfectComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have hcover : X.J.CoversTop
      (fun W : {W : Y.C // Y.HasStrictlyPerfectQuasiIso K W} => u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype u Y.J X.J hTop
      (Y.HasStrictlyPerfectQuasiIso K) hK
  rw [isPerfectComplex_iff]
  intro U
  refine ⟨(Sieve.ofObjects
    (fun W : {W : Y.C // Y.HasStrictlyPerfectQuasiIso K W} => u.obj W.val) U).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hcover U
  · rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
    exact hasStrictlyPerfectQuasiIso_of_hom X _ k
      (hasStrictlyPerfectQuasiIso_map u F G W (ηG W) (sq W) K hW)

/-! ### The transfer in the derived category -/

section Derived

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hDY : HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [hDX : HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hFlim : PreservesFiniteLimits F] [hFcolim : PreservesFiniteColimits F]

/-- **Perfectness in the derived category transfers along an exact additive functor with an exact
localization square.**  If `E` is a perfect object of `D(O')` then `F.mapDerivedCategory.obj E` is
a perfect object of `D(O)`.

A perfect object of `D(O')` is by definition the image of a perfect complex `K`; the degreewise
image `F K` is perfect by `isPerfectComplex_mapHomologicalComplex`, and its image in `D(O)` is
`F.mapDerivedCategory.obj E` because `CategoryTheory.Functor.mapDerivedCategory` of an exact
functor is induced by the degreewise functor
(`CategoryTheory.Functor.mapDerivedCategoryFactors`).

No derived functor is *constructed* here and no K-flat resolution appears: `F` is exact, so its
action on the derived category is the degreewise one, and the comparison between the two is
Mathlib's.  That is why this needs the underived square only. -/
theorem isPerfect_mapDerivedCategory [hu : u.IsContinuous Y.J X.J]
    (hTop : X.J.CoversTop u.obj)
    [hGadd : ∀ W : Y.C, (G W).Additive]
    [hGlim : ∀ W : Y.C, PreservesFiniteLimits (G W)]
    [hGcolim : ∀ W : Y.C, PreservesFiniteColimits (G W)]
    (ηG : ∀ W : Y.C,
      (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : ∀ W : Y.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    X.IsPerfect (F.mapDerivedCategory.obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    isPerfectComplex_mapHomologicalComplex u F G hTop ηG sq K hK, ⟨?_⟩⟩
  exact (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e

end Derived

end Transfer

/-! ### The transfer with the typeclass hypotheses passed explicitly -/

section Applied

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (u : Y.C ⥤ X.C)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (G : ∀ W : Y.C, SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⥤
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))

/-- `isPerfect_mapDerivedCategory` with the six functor-level typeclass hypotheses taken as
explicit arguments rather than synthesized.

This is not a weakening: the two statements have the same content, and this one is the form that
can be *applied*.  At a concrete pair of ringed sites the exactness and additivity of `F` and of
the `F_W` are proved at the spelling of the structure sheaves those functors were built with,
whereas the statement above asks for them at the spelling
`AlgebraicGeometry.RingedSite.ringSheaf` of the ringed sites.  The two spellings are equal by
`rfl` but `RingedSite.ringSheaf` does not reduce at instance transparency, so instance search does
not cross between them; passing the hypotheses explicitly replaces synthesis by a definitional
check, which does.  This is the same accommodation that
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses` makes, and
for the same reason. -/
theorem isPerfect_mapDerivedCategory_of_hypotheses
    (hFadd' : F.Additive) (hFlim' : PreservesFiniteLimits F)
    (hFcolim' : PreservesFiniteColimits F)
    (hGadd' : ∀ W : Y.C, (G W).Additive)
    (hGlim' : ∀ W : Y.C, PreservesFiniteLimits (G W))
    (hGcolim' : ∀ W : Y.C, PreservesFiniteColimits (G W))
    (hu' : u.IsContinuous Y.J X.J) (hTop : X.J.CoversTop u.obj)
    (ηG : ∀ W : Y.C,
      (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : ∀ W : Y.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    haveI := hFadd'
    haveI := hFlim'
    haveI := hFcolim'
    X.IsPerfect (F.mapDerivedCategory.obj E) := by
  have := hFadd'
  have := hFlim'
  have := hFcolim'
  have := hGadd'
  have := hGlim'
  have := hGcolim'
  have := hu'
  exact isPerfect_mapDerivedCategory u F G hTop ηG sq E hE

end Applied

end AlgebraicGeometry.RingedSite

end
