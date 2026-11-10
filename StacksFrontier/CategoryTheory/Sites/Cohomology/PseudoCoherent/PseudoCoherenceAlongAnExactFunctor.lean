module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence along a functor with an exact localization square

Let `(C, O)` and `(D, O')` be ringed sites, let `u : D ⥤ C` be a continuous functor whose image
covers the final object of `Sh(C)`, and let `F : Mod(O') ⥤ Mod(O)` be an additive functor.
Suppose that for every object `W` of `D` there is an exact additive
`F_W : Mod(O'|_W) ⥤ Mod(O|_{u(W)})` carrying the unit to the unit, together with a
*localization square*

```
  (- |_W) ⋙ F_W  ≅  F ⋙ (- |_{u(W)}) .
```

Then `F` carries an `m`-pseudo-coherent complex of `O'`-modules to an `m`-pseudo-coherent complex
of `O`-modules, degreewise.

This is the chain-level core of the argument of Stacks 08H4, isolated from the derived pullback.

## Why the square is a hypothesis and not derivable

`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` quantifies over the objects of the
site and asks for a strictly perfect complex on the *slice* over each member of a covering.  So
the hypothesis is a family of complexes on the slices of `D` and the conclusion is a family of
complexes on the slices of `C`, and a functor `Mod(O') ⥤ Mod(O)` does not act on slice categories
at all: without `F_W` and the square there is nothing to apply to the given approximation.  The
square is therefore irreducible input, not a convenience.

## What is *not* needed

Nothing here mentions a morphism of ringed topoi, a derived functor, or a K-flat resolution.

* Strict perfectness is carried by `SheafOfModules.isStrictlyPerfect_map` — any additive,
  finite-colimit-preserving functor with a unit isomorphism, at independent object and morphism
  universes — rather than by Stacks 08H3
  `AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules`, whose hypothesis is a
  `RingedToposHom`.  So neither `F` nor `F_W` has to be the pullback along a morphism of ringed
  topoi, and no exactness of `F` itself is used: only the `F_W` are asked to be exact.
  (`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` is the same statement but is
  not available here: its sections universe is fixed to `0`, so it does not apply at a general
  `w`.)
* The two cohomological conditions are carried because `F_W` is exact: an exact functor commutes
  with homology, so it preserves `CategoryTheory.QuasiIsoAt` and epimorphisms on homology.
* The covering is carried by `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype`, which
  is stated at independent object and morphism universes, so no smallness is imposed on either
  site.

Consequently the statement holds with the two sites' object and morphism universes independent,
sharing only the universe `w` of the sections of the two structure sheaves — the shape in which
the comparison `ε` of Stacks 08H7 lives.

## Which restriction functor

`(- |_W)` throughout is Mathlib's `SheafOfModules.overFunctor` for the slice topology
`CategoryTheory.GrothendieckTopology.over`, on the ring sheaf
`AlgebraicGeometry.RingedSite.ringSheaf` of the ringed site named in the statement;
`AlgebraicGeometry.RingedSite.restrictComplex` is its degreewise extension to cochain complexes,
and `SheafOfModules.overMap` is its analogue along an arrow of the site.  No other slice or
restriction functor is involved.

## Main results

* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectApproximation_of_hom`: a strictly perfect
  approximation over an object descends along an arrow into it.
* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectApproximation_map`: the square carries an
  approximation over `W` to one over `u(W)`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex`: the transfer
  of `m`-pseudo-coherence of complexes.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory` and
  `.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`: the same transfer in
  the derived category, for `F` exact.  This is the shape in which clause (1) ⇒ (2) of
  Stacks 08HE is stated, `ε` being flat so that its derived pullback is
  `CategoryTheory.Functor.mapDerivedCategory` of the underived one.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

/-! ### Transport of the two cohomological conditions

`isIso_homologyMap_of_iso`, `isIso_homologyMap_comp_iso` and `epi_homologyMap_comp_iso` are used
from `AlgebraicGeometry.RingedSite` (`PseudoCoherent/LocalNature.lean`), where they are public. -/

namespace ExactTransfer

section HomologyTransport

/-- A natural isomorphism of functors transports epimorphy of the image of a morphism: the two
images differ by composition with two isomorphisms. -/
private theorem epi_map_of_natIso {D E : Type*} [Category D] [Category E] {F₁ F₂ : D ⥤ E}
    (e : F₁ ≅ F₂) {A B : D} (f : A ⟶ B) (h : Epi (F₂.map f)) : Epi (F₁.map f) := by
  have heq : F₁.map f = e.hom.app A ≫ F₂.map f ≫ e.inv.app B := by
    rw [← Category.assoc, ← e.hom.naturality f, Category.assoc, e.hom_inv_id_app,
      Category.comp_id]
  have := h
  rw [heq]
  infer_instance

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {ℬ : Type*} [Category ℬ] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact additive functor preserves invertibility on cohomology in a degree: it preserves
`CategoryTheory.QuasiIsoAt`, which is invertibility of the map on homology. -/
private theorem isIso_homologyMap_mapHomologicalComplex
    {A B : CochainComplex 𝒜 ℤ} (α : A ⟶ B) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap α j)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) j) := by
  have : QuasiIsoAt α j := (quasiIsoAt_iff_isIso_homologyMap _ _).2 h
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- An exact additive functor preserves epimorphy on cohomology in a degree: the homology of the
image is the image of the homology, by `CategoryTheory.ShortComplex.homologyFunctorIso`, and an
exact functor preserves epimorphisms. -/
private theorem epi_homologyMap_mapHomologicalComplex
    {A B : CochainComplex 𝒜 ℤ} (α : A ⟶ B) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap α j)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) j) := by
  have := h
  have hFe : Epi (F.map (HomologicalComplex.homologyMap α j)) := inferInstance
  change Epi ((F.mapShortComplex ⋙ ShortComplex.homologyFunctor _).map
    ((HomologicalComplex.shortComplexFunctor _ _ j).map α))
  exact epi_map_of_natIso (ShortComplex.homologyFunctorIso F)
    ((HomologicalComplex.shortComplexFunctor _ _ j).map α) hFe

/-- The two cohomological conditions of an approximation `α` are preserved by an exact additive
functor followed by an isomorphism of the target. -/
private theorem homologyMap_conditions_map_comp_iso
    {A B : CochainComplex 𝒜 ℤ} {Q : CochainComplex ℬ ℤ} (α : A ⟶ B)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ≅ Q) (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) j)) ∧
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) m) :=
  ⟨fun j hj => isIso_homologyMap_comp_iso _ e j
    (isIso_homologyMap_mapHomologicalComplex F α j (hiso j hj)),
  epi_homologyMap_comp_iso _ e m (epi_homologyMap_mapHomologicalComplex F α m hepi)⟩

end HomologyTransport

section IsoTransport

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

end IsoTransport

end ExactTransfer

open ExactTransfer

/-! ### Strictly perfect approximations over one object -/

section Approximation

variable (X : RingedSite.{uX, vX, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] overMapLimits overMapColimits

/-- The datum that `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` asks for over one
object `V` of the site: a strictly perfect complex on the slice over `V` approximating `K|_V` in
degrees `> m`.  This is the body of that definition, named so that the two halves of the transfer
below can be stated separately. -/
def HasStrictlyPerfectApproximation
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (V : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
    ∃ α : P ⟶ X.restrictComplex K V,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)

/-- `m`-pseudo-coherence of a complex is: every object has a covering all of whose members carry
a strictly perfect approximation.  This holds by definition, and is stated so that the two
quantifiers are visible. -/
theorem isPseudoCoherentComplexFrom_iff
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) :
    X.IsPseudoCoherentComplexFrom K m ↔
      ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
        ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → X.HasStrictlyPerfectApproximation K m V :=
  Iff.rfl

/-- **A strictly perfect approximation descends along an arrow of the site.**  Restriction to a
smaller slice is exact and carries the unit to the unit, so it preserves strict perfectness
(`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`) and both cohomological
conditions, and it carries the restriction of the ambient complex to the smaller restriction
(`Stacks.SheafOfModules.overFunctorMapComplexIso`).

This is what makes a covering whose arrows have arbitrary sources usable. -/
theorem hasStrictlyPerfectApproximation_of_hom
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) {U V : X.C} (g : V ⟶ U)
    (h : X.HasStrictlyPerfectApproximation K m U) :
    X.HasStrictlyPerfectApproximation K m V := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  have hcmp : ((SheafOfModules.overMap.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (X.restrictComplex K U) ≅ X.restrictComplex K V :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (((SheafOfModules.overMap.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP
  exact ⟨_, hSP, _, homologyMap_conditions_map_comp_iso
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α hcmp m hiso hepi⟩

end Approximation

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

/-- The localization square read on cochain complexes.  Both sides are the degreewise extension
of a composite of two additive functors, so this is the given square under
`CategoryTheory.NatIso.mapHomologicalComplex`, with the two composites reassociated by
`CategoryTheory.Functor.mapHomologicalComplexCompIso` at the identity. -/
def squareComplexIso (W : Y.C) [(G W).Additive]
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W)) :
    (SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (G W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (u.obj W)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙
        G W)) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex sq (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (u.obj W)))
        (ComplexShape.up ℤ)).symm

/-- **The image of a strictly perfect approximation is one over the image object.**  Apply `F_W`
degreewise: strict perfectness is preserved because `F_W` is additive, preserves finite colimits
and carries the unit to the unit; the two cohomological conditions are preserved because `F_W` is
exact; and the target is identified with `(F K)|_{u(W)}` by the localization square. -/
theorem hasStrictlyPerfectApproximation_map (W : Y.C) [(G W).Additive]
    [PreservesFiniteLimits (G W)] [PreservesFiniteColimits (G W)]
    (ηG : (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (m : ℤ)
    (h : Y.HasStrictlyPerfectApproximation K m W) :
    X.HasStrictlyPerfectApproximation
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m (u.obj W) := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W))
      (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w} (G W) ηG hP
  have hcmp := (squareComplexIso u F G W sq).app K
  exact ⟨_, hSP, _, homologyMap_conditions_map_comp_iso (G W) α hcmp m hiso hepi⟩

/-- **Pseudo-coherence of complexes transfers along an additive functor with an exact
localization square.**  If `K` is an `m`-pseudo-coherent complex of `O'`-modules then the
degreewise image `F K` is an `m`-pseudo-coherent complex of `O`-modules.

The covering of an object `U` of `C` that the conclusion asks for is the sieve of arrows
factoring through some `u(W)` with `W` carrying a strictly perfect approximation of `K|_W`; it is
covering by `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype`, which refines the given
covering of the final object by the `u(W)` to those `W`.  Over such a `u(W)` the approximation is
carried across by `F_W` (`hasStrictlyPerfectApproximation_map`), and along an arrow `V ⟶ u(W)` it
descends (`hasStrictlyPerfectApproximation_of_hom`), which is what the arrows of that covering
supply. -/
theorem isPseudoCoherentComplexFrom_mapHomologicalComplex [hu : u.IsContinuous Y.J X.J]
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
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (m : ℤ)
    (hK : Y.IsPseudoCoherentComplexFrom K m) :
    X.IsPseudoCoherentComplexFrom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
  have hcover : X.J.CoversTop
      (fun W : {W : Y.C // Y.HasStrictlyPerfectApproximation K m W} => u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype u Y.J X.J hTop
      (Y.HasStrictlyPerfectApproximation K m) hK
  rw [isPseudoCoherentComplexFrom_iff]
  intro U
  refine ⟨(Sieve.ofObjects
    (fun W : {W : Y.C // Y.HasStrictlyPerfectApproximation K m W} => u.obj W.val) U).arrows,
    ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hcover U
  · rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
    exact hasStrictlyPerfectApproximation_of_hom X _ m k
      (hasStrictlyPerfectApproximation_map u F G W (ηG W) (sq W) K m hW)

/-! ### The transfer in the derived category -/

section Derived

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hDY : HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [hDX : HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hFlim : PreservesFiniteLimits F] [hFcolim : PreservesFiniteColimits F]

/-- **Pseudo-coherence in the derived category transfers along an exact additive functor with an
exact localization square.**  If `E` is an `m`-pseudo-coherent object of `D(O')` then
`F.mapDerivedCategory.obj E` is an `m`-pseudo-coherent object of `D(O)`.

An `m`-pseudo-coherent object of `D(O')` is by definition the image of an `m`-pseudo-coherent
complex `K`; the degreewise image `F K` is `m`-pseudo-coherent by
`isPseudoCoherentComplexFrom_mapHomologicalComplex`, and its image in `D(O)` is
`F.mapDerivedCategory.obj E` because `CategoryTheory.Functor.mapDerivedCategory` of an exact
functor is induced by the degreewise functor
(`CategoryTheory.Functor.mapDerivedCategoryFactors`).

No derived functor is *constructed* here and no K-flat resolution appears: `F` is exact, so its
action on the derived category is the degreewise one, and the comparison between the two is
Mathlib's.  That is why this needs the underived square only. -/
@[sga "6 I 2.13" "special case"]
theorem isPseudoCoherentFrom_mapDerivedCategory [hu : u.IsContinuous Y.J X.J]
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
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (m : ℤ)
    (hE : Y.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj E) m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    isPseudoCoherentComplexFrom_mapHomologicalComplex u F G hTop ηG sq K m hK, ⟨?_⟩⟩
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

/-- `isPseudoCoherentFrom_mapDerivedCategory` with the six functor-level typeclass hypotheses
taken as explicit arguments rather than synthesized.

This is not a weakening: the two statements have the same content, and this one is the form that
can be *applied*.  At a concrete pair of ringed sites the exactness and additivity of `F` and of
the `F_W` are available at the spelling of the structure sheaves those functors were built with,
whereas the statement above asks for them at the spelling
`AlgebraicGeometry.RingedSite.ringSheaf` of the ringed sites.  The two spellings are equal by
`rfl` but `RingedSite.ringSheaf` does not reduce at instance transparency, so instance search
does not cross between them — the same obstruction that forces
`AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite` to exist.
Passing the hypotheses explicitly replaces synthesis by a definitional check, which does
cross. -/
theorem isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses
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
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (m : ℤ)
    (hE : Y.IsPseudoCoherentFrom E m) :
    haveI := hFadd'
    haveI := hFlim'
    haveI := hFcolim'
    X.IsPseudoCoherentFrom (F.mapDerivedCategory.obj E) m := by
  have := hFadd'
  have := hFlim'
  have := hFcolim'
  have := hGadd'
  have := hGlim'
  have := hGcolim'
  have := hu'
  exact isPseudoCoherentFrom_mapDerivedCategory u F G hTop ηG sq E m hE

end Applied

end AlgebraicGeometry.RingedSite

end
