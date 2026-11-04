module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.ModuleCohomologyDeltaFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback map on module cohomology along a continuous map is a morphism of δ-functors

`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor R V` is the long exact cohomology sequence
over an open `V` for sheaves of `R`-modules, with degree-`n` component `Hfunctor R V n`.  What this
file supplies is the comparison of that δ-functor with cohomology over an open of *another space*
along a continuous map: **the pullback maps on module cohomology are the components of a morphism
of δ-functors, hence commute with the connecting morphism.**

This is the module counterpart of
`Stacks.Cohomology.AbelianColimit.H'spacePullback_comp_H'δ`, which is the same statement for
abelian sheaves and was the only form available.

## The hypotheses, and why there is no flatness

The obvious route is to pull sheaves of modules back along a morphism of ringed spaces and
compare `Hⁿ(V, F)` with `Hⁿ(U, f^* F)`.  That route **cannot avoid flatness**:
`CategoryTheory.DeltaFunctor.precomp` — and equally `ModuleSheafCohomology.extDeltaFunctor` —
needs its comparison functor to be *exact* merely to **state** the target as a δ-functor, and
`RingedSpaceModuleAdjunction.modulePullback` is only right exact in general (Stacks 01AJ (2)); its
exactness is `RingedSpaceModuleAdjunction.exactFunctor_modulePullback_of_isFlat` and genuinely
needs `f` flat.

The flatness is avoidable by forgetting the module structure **first**.  The comparison functor
used here is

```
underlyingPullback f R =
  SheafOfModules.toSheaf R ⋙ Stacks.Cohomology.AbelianColimit.sheafPullback f
```

the forgetful functor to abelian sheaves followed by the inverse image of *abelian* sheaves.  Both
halves are exact with no hypothesis at all: `SheafOfModules.toSheaf` is the exact forgetful functor
that `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` runs on, and the abelian inverse
image is exact by Stacks 01AJ (3)
(`RingedSpaceModuleAdjunction.exactFunctor_sheafPullback`).  So the statements below ask only that
`f` be a continuous map of topological spaces and that `U ⊆ f⁻¹ V`.  **No flatness, and not even a
morphism of ringed spaces**: the ring data enters only through the morphism of sequences that a
consumer supplies afterwards, never through the δ-compatibility.

## What this does not give, and why — two negative results

**The no-flatness statement cannot land in module cohomology on `X`.**  Its target is the
*abelian* cohomology `H'ⁿ(U, f⁻¹ F_ab)`, and that is forced by the same obstruction: to state
module cohomology over `U` as a δ-functor on `Mod(R)` one has to precompose it with a functor
`Mod(R) ⥤ Mod(R')`, and `CategoryTheory.DeltaFunctor.precomp` needs that functor exact.  There is
no exact functor `Mod(R) ⥤ Mod(R')` attached to a bare continuous map.  So the return trip from
abelian cohomology over `U` to module cohomology over `U` is Stacks 03FD and nothing weaker — the
δ-compatible form of it, whose site-level instantiation
`StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparisonDef.lean` records as
still open.  A reader who tries to push the statement below into module cohomology on `X` without
that will rediscover this; it is not a matter of finding the right `rfl`.

**Flatness is not merely avoidable here, it is unavailable in the motivating application.**  The
morphism relating the two spaces in condition (ii) of Stacks 07YG for the sections obstruction
theory — `Deformation.Artin.SectionsSheaf.immersion`, i.e.
`Deformation.Artin.SectionsSheaf.baseChangeMap` at the quotient map of a deformation situation —
is a *thickening*: it is carried through that development as
`AlgebraicGeometry.IsClosedImmersion`, and a closed immersion is flat only degenerately.  So the
flat instantiation of `comparisonHom` below (`Ψ = RingedSpaceModuleAdjunction.modulePullback f`
with `f` flat) is **not** the one that application can use, and
`Deformation.Artin.SectionsSheaf.isFlatOver_baseChange` does not help: it is flatness of the
*sheaf* over the *structure* morphism, not flatness of the morphism between the two base changes.
What that application has instead is exactness of the *pushforward* along a closed immersion.
**That route is built**, in
`StacksFrontier/Topology/Sheaves/Cohomology/ModuleSpacePullback/Pushforward.lean`: it stays in
module cohomology on both sides, needs no Stacks 03FD, and its acyclicity input (Stacks 01EX
part (2)) holds for an arbitrary morphism of ringed spaces.  For a thickening it is that file,
not this one, that a consumer wants.

## Where the mathematics is

Almost nowhere, and that is the point.  `cohomologyDeltaFunctor R V` is *universal* (Stacks 010S,
`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor_isUniversal`), so by
`CategoryTheory.DeltaFunctor.IsUniversal.lift` a natural transformation in degree zero extends to a
morphism of δ-functors, uniquely.  Commuting with the connecting morphisms is then a *field* of
that morphism rather than a theorem to prove.  So the only new input is the degree-zero map

`abSectionsPullback f V U h : abSections V ⟶ sheafPullback f ⋙ abSections U`,

the pullback map on sections of abelian sheaves: a section of `G` over `V` goes to its image under
the adjunction unit `G ⟶ f_* f⁻¹ G`, whose value over `V` is a section of `f⁻¹ G` over `f⁻¹ V`, and
then restricts to `U`.  That is elementary, and is stated for abelian sheaves alone so that it can
be reused.

## Main definitions

* `Stacks.Cohomology.ModuleSpacePullback.abSectionsPullback`: the pullback map on sections of
  abelian sheaves along a continuous map, `Γ(V, G) ⟶ Γ(U, f⁻¹ G)` for `U ≤ f⁻¹ V`, natural in `G`.
* `Stacks.Cohomology.ModuleSpacePullback.H'functorZeroIso`: native cohomology in degree zero is
  sections, `H'functor U 0 ≅ abSections U`.  This is `ModuleSheafCohomology.extZeroIsoCoyoneda`
  read through the corepresentation of sections.
* `Stacks.Cohomology.ModuleSpacePullback.underlyingPullback`: the exact comparison functor
  `Mod(R) ⥤ Ab(X)`, forgetting the module structure and then taking the abelian inverse image.
* `Stacks.Cohomology.ModuleSpacePullback.sectionsPullback`: the degree-zero comparison
  `Hfunctor R V 0 ⟶ underlyingPullback f R ⋙ H'functor U 0`.
* `Stacks.Cohomology.ModuleSpacePullback.deltaHom`: **the morphism of δ-functors**
  `cohomologyDeltaFunctor R V ⟶ (H'deltaFunctor U).precomp (underlyingPullback f R)`.
* `Stacks.Cohomology.ModuleSpacePullback.map`: its degree-`n` component, the pullback map
  `Hⁿ(V, F) ⟶ Hⁿ(U, f⁻¹ F_ab)` on module cohomology.

## Main results

* `Stacks.Cohomology.ModuleSpacePullback.map_zero` and
  `Stacks.Cohomology.ModuleSpacePullback.deltaHom_unique`: the morphism of δ-functors is the
  *unique* one extending the pullback map on sections.  This is what pins it down; by Stacks 010S
  a morphism out of a universal δ-functor is determined by its degree-zero component.
* `Stacks.Cohomology.ModuleSpacePullback.map_comp_H'δ`: **the pullback map on module cohomology
  commutes with the connecting morphism.**
* `Stacks.Cohomology.ModuleSpacePullback.map_map_comp_H'δ`: the same square for a short exact
  sequence of modules upstairs, one of abelian sheaves downstairs, and a morphism between the
  image of the first and the second — the form a comparison of two long exact sequences across a
  map of spaces takes.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ModuleSheafCohomology
open Stacks.Cohomology.AbelianColimit

namespace Stacks.Cohomology.ModuleSpacePullback

universe u

/-! ### The pullback map on sections of abelian sheaves -/

section Sections

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V)

/-- **The pullback map on sections of abelian sheaves along a continuous map.**  A section of `G`
over `V` is carried by the unit `G ⟶ f_* f⁻¹ G` of the inverse-image/direct-image adjunction to a
section of `f⁻¹ G` over `f⁻¹ V` — the identification `(f_* H)(V) = H(f⁻¹ V)` being definitional —
and then restricted to `U ≤ f⁻¹ V`.  Natural in `G`.

This is the degree-zero input of `deltaHom`, and the only new mathematics in this file. -/
def abSectionsPullback : abSections V ⟶ sheafPullback f ⋙ abSections U :=
  Functor.whiskerRight (Stacks.Cohomology.ExtComparison.Spaces.sheafAdjunction f).unit
      (abSections V) ≫
    Functor.whiskerLeft (sheafPullback f)
      ((sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map (homOfLE h).op)

end Sections

/-! ### Native cohomology in degree zero is sections -/

section DegreeZero

variable {Z : Type u} [TopologicalSpace Z]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]

/-- **Native cohomology over an open in degree zero is sections over that open**, as an
isomorphism of functors: `Ext⁰` out of a corepresenting object is the corepresented functor
(`ModuleSheafCohomology.extZeroIsoCoyoneda`), and sections over `U` are corepresented by
`freeOfOpen U` (`ModuleSheafCohomology.evaluationRepresentation`). -/
def H'functorZeroIso (U : Opens Z) : H'functor U 0 ≅ abSections U :=
  extZeroIsoCoyoneda (freeOfOpen U) ≪≫
    (evaluationRepresentation (Opens.grothendieckTopology Z) U).symm

end DegreeZero

/-! ### The exact comparison functor -/

section Comparison

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (R : Sheaf (Opens.grothendieckTopology ↥Y) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]

/-- **The exact comparison functor**: forget the module structure, then take the inverse image of
abelian sheaves.  Both halves are exact unconditionally, which is why nothing below needs `f` to
be flat, or even to be a morphism of ringed spaces; see the module docstring. -/
abbrev underlyingPullback : SheafOfModules.{u} R ⥤
    Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ sheafPullback f

end Comparison

/-! ### The comparison of module cohomology with any δ-functor along an exact functor -/

section Universal

open Stacks.Cohomology.ModuleDelta

universe u' v'

variable {Z : Type u} [TopologicalSpace Z]
  (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (V : Opens Z)
  {A : Type u'} [Category.{v'} A] [Abelian A]
  (Ψ : SheafOfModules.{u} R ⥤ A) [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ]
  (G : DeltaFunctor A AddCommGrpCat.{u})

/-- **The comparison of module cohomology over an open with an arbitrary δ-functor along an
arbitrary exact functor, determined by its degree-zero component.**  This is the reusable
primitive: module cohomology over `V` is a *universal* δ-functor (Stacks 010S), so a natural
transformation `τ` in degree zero extends to a morphism of δ-functors, uniquely, and commuting
with the connecting morphisms is a *field* of the result rather than a theorem.

The hypotheses are exactly what the construction needs and no more.  `Ψ` must be exact, because
`CategoryTheory.DeltaFunctor.precomp` needs that merely to **state** `Ψ ⋙ Gⁿ` as a δ-functor on
`Mod(R)`; nothing else is assumed of `Ψ`, of `A` or of `G`.  Three instantiations are intended,
and the choice of `Ψ` is where the geometry lives: the inverse image of *abelian* sheaves after
forgetting the module structure, which is exact unconditionally (`deltaHom` below); the pullback
of sheaves of modules along a *flat* morphism of ringed spaces; and the pushforward of sheaves of
modules along a morphism whose pushforward is exact. -/
def comparisonHom (τ : Hfunctor R V 0 ⟶ Ψ ⋙ G.functor 0) :
    cohomologyDeltaFunctor R V ⟶ G.precomp Ψ :=
  DeltaFunctor.IsUniversal.lift (cohomologyDeltaFunctor R V) τ

/-- The degree-zero component of `comparisonHom` is the transformation it was built from. -/
@[simp]
theorem comparisonHom_app_zero (τ : Hfunctor R V 0 ⟶ Ψ ⋙ G.functor 0) :
    (comparisonHom R V Ψ G τ).app 0 = τ :=
  DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- **`comparisonHom` is the unique morphism of δ-functors with the given degree-zero
component**, by Stacks 010S. -/
theorem comparisonHom_unique (τ : Hfunctor R V 0 ⟶ Ψ ⋙ G.functor 0)
    (η : cohomologyDeltaFunctor R V ⟶ G.precomp Ψ) (hη : η.app 0 = τ) :
    η = comparisonHom R V Ψ G τ :=
  DeltaFunctor.IsUniversal.hom_ext_zero _
    (hη.trans (comparisonHom_app_zero R V Ψ G τ).symm)

/-- **The comparison commutes with the connecting morphisms.**  For a short exact sequence `S` of
sheaves of `R`-modules, the connecting morphism of module cohomology over `V` followed by the
comparison in degree `n₁` is the comparison in degree `n₀` followed by the connecting morphism of
`G` at the image sequence `Ψ(S)`. -/
theorem comparisonHom_comp_δ (τ : Hfunctor R V 0 ⟶ Ψ ⋙ G.functor 0)
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (n : ℕ) :
    ((comparisonHom R V Ψ G τ).app n).app S.X₃ ≫ G.δ (hS.map_of_exact Ψ) n =
      (cohomologyDeltaFunctor R V).δ hS n ≫
        ((comparisonHom R V Ψ G τ).app (n + 1)).app S.X₁ :=
  (comparisonHom R V Ψ G τ).comm hS n

end Universal

/-! ### The morphism of δ-functors along a continuous map, and δ-naturality -/

section DeltaHom

open Stacks.Cohomology.ModuleDelta

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (R : Sheaf (Opens.grothendieckTopology ↥Y) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V)

/-- **The degree-zero comparison**: the pullback map on sections of abelian sheaves, read between
cohomology in degree zero on both sides.  On the source, degree-zero cohomology is sections by
left exactness (`CategoryTheory.Functor.rightDerivedZeroIsoSelf`); on the target it is sections by
`H'functorZeroIso`. -/
def sectionsPullback : Hfunctor R V 0 ⟶ underlyingPullback f R ⋙ H'functor U 0 :=
  (secF R V).rightDerivedZeroIsoSelf.hom ≫
    Functor.whiskerLeft (SheafOfModules.toSheaf R) (abSectionsPullback f V U h) ≫
      Functor.whiskerLeft (underlyingPullback f R) (H'functorZeroIso U).inv

/-- **The pullback map on module cohomology along a continuous map, as a morphism of
δ-functors.**  The source is the long exact cohomology sequence over `V` for sheaves of
`R`-modules, which is a *universal* δ-functor (Stacks 010S); the target is native cohomology over
`U` of abelian sheaves on the source space, precomposed with the exact comparison functor
`underlyingPullback f R`.  By universality the degree-zero map `sectionsPullback` extends to a
morphism of δ-functors, uniquely — and a morphism of δ-functors is precisely a family of maps
commuting with the connecting morphisms.

No flatness and no morphism of ringed spaces is involved; see the module docstring. -/
def deltaHom : cohomologyDeltaFunctor R V ⟶
    (H'deltaFunctor U).precomp (underlyingPullback f R) :=
  comparisonHom R V (underlyingPullback f R) (H'deltaFunctor U) (sectionsPullback f R V U h)

/-- **The pullback map on module cohomology in degree `n`**, `Hⁿ(V, F) ⟶ Hⁿ(U, f⁻¹ F_ab)`,
natural in the sheaf of `R`-modules `F`. -/
def map (n : ℕ) : Hfunctor R V n ⟶ underlyingPullback f R ⋙ H'functor U n :=
  (deltaHom f R V U h).app n

/-- In degree zero the pullback map on cohomology is the pullback map on sections. -/
@[simp]
theorem map_zero : map f R V U h 0 = sectionsPullback f R V U h :=
  comparisonHom_app_zero R V (underlyingPullback f R) (H'deltaFunctor U)
    (sectionsPullback f R V U h)

/-- **`deltaHom` is the unique morphism of δ-functors extending the pullback map on sections.**
This is what pins the family of maps down: by Stacks 010S a morphism out of a universal δ-functor
is determined by its degree-zero component. -/
theorem deltaHom_unique
    (η : cohomologyDeltaFunctor R V ⟶ (H'deltaFunctor U).precomp (underlyingPullback f R))
    (hη : η.app 0 = sectionsPullback f R V U h) : η = deltaHom f R V U h :=
  comparisonHom_unique R V (underlyingPullback f R) (H'deltaFunctor U)
    (sectionsPullback f R V U h) η hη

/-- **The pullback map on module cohomology commutes with the connecting morphism.**  For a short
exact sequence `S` of sheaves of `R`-modules on `Y`, an open `V ⊆ Y`, an open `U ⊆ f⁻¹ V` and
`n₀ + 1 = n₁`, the square

    Hⁿ⁰(V, S.X₃) ⟶ Hⁿ¹(V, S.X₁)
         ↓                ↓
    Hⁿ⁰(U, f⁻¹S.X₃) ⟶ Hⁿ¹(U, f⁻¹S.X₁)

commutes, the horizontal arrows being the connecting morphisms — above, that of module cohomology
over `V`; below, `H'δ` of the image sequence of abelian sheaves on `X` — and the vertical arrows
the pullback maps.

This is the module counterpart of
`Stacks.Cohomology.AbelianColimit.H'spacePullback_comp_H'δ`, and it carries no flatness
hypothesis. -/
theorem map_comp_H'δ
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (n : ℕ) :
    (map f R V U h n).app S.X₃ ≫
        H'δ (hS.map_of_exact (underlyingPullback f R)) U (rfl : n + 1 = n + 1) =
      (cohomologyDeltaFunctor R V).δ hS n ≫ (map f R V U h (n + 1)).app S.X₁ :=
  comparisonHom_comp_δ R V (underlyingPullback f R) (H'deltaFunctor U)
    (sectionsPullback f R V U h) hS n

/-- **The comparison of the two long exact sequences across a continuous map.**  Given a short
exact sequence `S` of sheaves of `R`-modules on `Y`, a short exact sequence `T` of abelian sheaves
on `X`, and a morphism `Φ : f⁻¹ S_ab ⟶ T`, the maps on cohomology commute with the connecting
morphisms of the two sequences.  It is `map_comp_H'δ` followed by the naturality of `H'δ` in the
short exact sequence (`Stacks.Cohomology.AbelianColimit.H'δ_naturality`). -/
@[ega "0 12.1.6" "more general"]
theorem map_map_comp_H'δ
    {S : ShortComplex (SheafOfModules.{u} R)}
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hT : T.ShortExact) (Φ : S.map (underlyingPullback f R) ⟶ T) (n : ℕ) :
    ((map f R V U h n).app S.X₃ ≫ (H'functor U n).map Φ.τ₃) ≫
        H'δ hT U (rfl : n + 1 = n + 1) =
      (cohomologyDeltaFunctor R V).δ hS n ≫
        ((map f R V U h (n + 1)).app S.X₁ ≫ (H'functor U (n + 1)).map Φ.τ₁) := by
  rw [Category.assoc, H'δ_naturality U (hS.map_of_exact (underlyingPullback f R)) hT Φ rfl,
    ← Category.assoc, map_comp_H'δ f R V U h hS n]
  exact Category.assoc _ _ _

end DeltaHom

end Stacks.Cohomology.ModuleSpacePullback

end
