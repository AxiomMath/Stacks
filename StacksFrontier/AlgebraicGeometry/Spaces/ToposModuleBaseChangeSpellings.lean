module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeHorizontal
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeIdentity

/-!
# The two spellings of the degree-zero base change map agree

For a commutative square

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

of algebraic spaces the degree-zero base change map `g^*f_* ⟶ f'_*(g')^*` is written twice in
this development, because the *direct* image is:

* `AlgebraicGeometry.Space.moduleBaseChangeMap` uses the modules development's direct image
  `AlgebraicGeometry.Space.modulePushforward`, which takes the direct image of sheaves first and
  restricts scalars along the direct-image form `𝒪_Y ⟶ f_*𝒪_X` of the structure map.  This is the
  spelling the higher direct images `R^if_*` and the chart computations are stated at, and it is
  the spelling `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat` — the degree-zero
  clause of **Stacks 073K**, part (1) — is proved at.
* `AlgebraicGeometry.Space.toposModuleBaseChangeMap` uses the ringed-topoi direct image
  `AlgebraicGeometry.Space.toposModulePushforward`, which restricts scalars along the
  inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` first.  This is the spelling the base change map of
  **Stacks 0736** on bounded below derived categories is built from, and the one the pasting law
  of **Stacks 0E47** is stated at.

The two direct images agree up to `AlgebraicGeometry.Space.modulePushforwardIso`, the
direct-image half of **Stacks 03LU**.  The *inverse* images need no crossing:
`AlgebraicGeometry.Space.modulePullback` is by definition
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale ringed topoi.

This file crosses the two spellings at the base change map itself, and draws the consequence for
the degree-zero clause of **Stacks 073K**, part (1): it holds at the ringed-topoi spelling too.

## Main results

* `Stacks.Cohomology.BaseChange.mate_ofNatIsoRight`: **the generic crossing.**  A base change
  mate is carried across a transport of the right adjoints of its two adjunctions along
  isomorphisms, together with the corresponding conjugation of its comparison of composite right
  adjoints, by whiskering with the two comparison isomorphisms of the middle functors.
* `AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_moduleBaseChangeMap`: **the two base
  change maps agree modulo `AlgebraicGeometry.Space.modulePushforwardIso`**, and
  `…_app_eq` is the same identity at an object.
* `AlgebraicGeometry.Space.isIso_toposModuleBaseChangeMap_app_of_isFlat`: **the degree-zero
  clause of Stacks 073K, part (1), at the ringed-topoi spelling** — for a cartesian square with
  `g` flat and `f` quasi-compact and quasi-separated, `toposModuleBaseChangeMap` is invertible at
  every quasi-coherent `𝒪_X`-module.

## Implementation notes

*Why the crossing is a single generic application.*  Both base change maps are the same
construction `Stacks.Cohomology.BaseChange.mate` of three ingredients, and all three differ by a
transport along `modulePushforwardIso`:

* the two vertical adjunctions.  `AlgebraicGeometry.Space.modulePullbackAdjunction` is by
  definition `AlgebraicGeometry.Space.toposModulePullbackAdjunction` with its right adjoint read
  through `modulePushforwardIso`, i.e. `CategoryTheory.Adjunction.ofNatIsoRight` of it;
* the two direct images in the middle, which differ by `modulePushforwardIso` directly;
* the comparison of the two composite direct images.
  `AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso` is *defined* as
  `AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso` conjugated by the four
  comparisons, in exactly the shape the generic lemma below asks for.

So the identification is `mate_ofNatIsoRight` applied once, with
`AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mate` rewritten with first so that the module
spelling is already presented as a mate.  No property of `modulePushforwardIso` is used, and the
geometric content — the associativity pentagon of **Stacks 03LU**, and the chart computation of
the degree-zero clause — stays where it was proved.

*Why the generic lemma is stated with everything as a variable.*  Each of its two mates mentions
two adjunctions, four functors and a comparison, and at the small étale ringed topoi of algebraic
spaces those are terms whose crossings accumulate: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleBaseChangeHorizontal.lean` record statements at
this seating that reach `maximum recursion depth` or time out in `isDefEq` for no reason other
than that accumulation.  With the functors as variables the proof is three naturality squares and
the geometric application is one `exact`;  both check in well under a second.  The lemma belongs
beside `Stacks.Cohomology.BaseChange.mate` and is stated here, in its only consumer, for the same
reason the mate calculus of
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/BaseChangeMatePasting.lean` is stated
generically there.

*Which adjunction the crossing is taken at.*  `toposModulePullbackAdjunction` rather than the
generic `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`:  its declared type is
`modulePullback … ⊣ toposModulePushforward …`, so every category in the application is the
modules development's `AlgebraicGeometry.Space.Modules` and there is nothing to cross at a
category position.  That is the seating the whole of this chain uses, for the reason its
implementation notes record.

*What this does not do: the derived crossing.*  Nothing here identifies the degree-zero
cohomology of `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` — the base change map of
**Stacks 0736** on `D⁺` — with the underived `toposModuleBaseChangeMap` it descends from.  Until
that is done, this file does not give degree zero of the map **Stacks 073K**, part (1) is about,
which is `AlgebraicGeometry.Space.higherDirectImageBaseChangeMap` in degree `0`;  it gives degree
zero of the underived map that one descends from.  The same absence is recorded, for the
corresponding comparison map of **Stacks 0GN5** at a square of schemes, in the implementation
notes of `StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/DegreewiseComparison.lean`.

The route is nevertheless mapped out, and every input it needs is proved and public.
`Stacks.Cohomology.BaseChange.derived_fac_app` pins the descended map through the derived-functor
unit of `Rf_*`, and `Stacks.Cohomology.BaseChange.onHomotopy_app` writes the other side of that
equation as four factors.  Applying `CategoryTheory.DerivedCategory.Plus.homologyFunctor _ 0` to
it at `𝓕` placed in degree zero, three of those four factors become isomorphisms —
`Stacks.Cohomology.BaseChange.exactUnit_isIso` for the inverse images, which are exact for a flat
`g` by **Stacks 04JC**, and
`CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`
(**Stacks 05TD**, part (3)) for the direct images, which are left exact being right adjoints —
and the left-hand side becomes an isomorphism by the same two facts through
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`.  What is left is the fourth factor,
`Stacks.Cohomology.BaseChange.mapPlus` of the underived map at a complex concentrated in degree
zero;  identifying its degree-zero cohomology with the underived map at `𝓕` is the one step that
has no available input, and it is a statement about a single complex and not about this square.

*No `@[stacks 073K]` attribute.*  Part (1) of **Stacks 073K** quantifies over all `i ≥ 0` and is
asserted of the map of higher direct images;  what is proved here is its degree-zero clause, at
one of the two spellings of the degree-zero base change map, so it is an input to the tag and not
an assertion of it.  The same convention is followed by the module spelling
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`, and the part-(2) carrier
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` is untouched.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChange

section MateSpelling

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- **A base change mate is carried across a transport of the right adjoints of its two
adjunctions.**  Let `adj : G ⊣ P` and `adj' : G' ⊣ P'` be the two adjunctions a base change mate
is taken across, let `i : P ≅ Q` and `i' : P' ≅ Q'` transport their right adjoints, and let
`j : F ≅ H` and `j' : F' ≅ H'` compare the two middle functors.  A comparison
`e : Q' ⋙ H ≅ H' ⋙ Q` of the two composite right adjoints at the second reading gives one at the
first by conjugating with those four isomorphisms, and the two resulting mates agree up to
whiskering by `j` and `j'`.

Nothing is assumed of the six isomorphisms:  the identity is the naturality of `j` at the unit of
`adj'`, the naturality of `i.inv` at `j'`, and the naturality of the counit of `adj` at `j'`.

The conjugation of `e` is written out rather than taken as a hypothesis because that is the shape
the consumer's comparison is defined in;  see
`AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso`. -/
theorem mate_ofNatIsoRight {G : B ⥤ D} {P Q : D ⥤ B} (adj : G ⊣ P) (i : P ≅ Q)
    {G' : A ⥤ C} {P' Q' : C ⥤ A} (adj' : G' ⊣ P') (i' : P' ≅ Q')
    {F H : A ⥤ B} (j : F ≅ H) {F' H' : C ⥤ D} (j' : F' ≅ H')
    (e : Q' ⋙ H ≅ H' ⋙ Q) :
    mate adj adj' F F'
        ((Functor.isoWhiskerLeft P' j ≪≫ Functor.isoWhiskerRight i' H) ≪≫ e ≪≫
          (Functor.isoWhiskerLeft F' i ≪≫ Functor.isoWhiskerRight j' Q).symm) =
      Functor.whiskerRight j.hom G ≫
        mate (adj.ofNatIsoRight i) (adj'.ofNatIsoRight i') H H' e ≫
        Functor.whiskerLeft G' j'.inv := by
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, mate_app,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, Functor.map_comp, Category.assoc]
  have h1 : G.map (F.map (adj'.unit.app X)) ≫ G.map (j.hom.app (P'.obj (G'.obj X))) =
      G.map (j.hom.app X) ≫ G.map (H.map (adj'.unit.app X)) := by
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (j.hom.naturality (adj'.unit.app X))
  have h2 : G.map (Q.map (j'.inv.app (G'.obj X))) ≫
        G.map (i.inv.app (F'.obj (G'.obj X))) ≫ adj.counit.app (F'.obj (G'.obj X)) =
      G.map (i.inv.app (H'.obj (G'.obj X))) ≫
        adj.counit.app (H'.obj (G'.obj X)) ≫ j'.inv.app (G'.obj X) := by
    rw [← Category.assoc, ← G.map_comp, i.inv.naturality (j'.inv.app (G'.obj X)), G.map_comp,
      Category.assoc, adj.counit_naturality (j'.inv.app (G'.obj X))]
  rw [reassoc_of% h1, h2]

end MateSpelling

end Stacks.Cohomology.BaseChange

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y X' Y' : AlgebraicSpaces B S hS}

section Square

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The two spellings of the degree-zero base change map of a square of algebraic spaces
agree.**  `AlgebraicGeometry.Space.toposModuleBaseChangeMap`, whose direct images are the
ringed-topoi ones, is `AlgebraicGeometry.Space.moduleBaseChangeMap`, whose direct images are the
modules development's, read through the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of **Stacks 03LU** at `f` and at `f'`.

It is `Stacks.Cohomology.BaseChange.mate_ofNatIsoRight` applied once:  the module spelling is
presented as a mate by `AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mate`, its two adjunctions
are the ones here with their right adjoints transported along `modulePushforwardIso`, and its
comparison of the two composite direct images is the one here conjugated by the four comparisons
— which is how `AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso` is defined. -/
theorem toposModuleBaseChangeMap_eq_moduleBaseChangeMap (comm : g' ≫ f = f' ≫ g) :
    toposModuleBaseChangeMap f g f' g' comm =
      Functor.whiskerRight (modulePushforwardIso B S hS f).hom (modulePullback B S hS g) ≫
        moduleBaseChangeMap f g f' g' comm ≫
        Functor.whiskerLeft (modulePullback B S hS g') (modulePushforwardIso B S hS f').inv := by
  rw [moduleBaseChangeMap_eq_mate f g f' g' comm]
  exact Stacks.Cohomology.BaseChange.mate_ofNatIsoRight
    (toposModulePullbackAdjunction g) (modulePushforwardIso B S hS g)
    (toposModulePullbackAdjunction g') (modulePushforwardIso B S hS g')
    (modulePushforwardIso B S hS f) (modulePushforwardIso B S hS f')
    (modulePushforwardSquareComparisonIso f g f' g' comm)

/-- `AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_moduleBaseChangeMap` at an
`𝒪_X`-module:  the two whiskerings become the comparison of **Stacks 03LU** at `f`, pushed into
`g^*`, and its inverse at `f'`, evaluated at `(g')^*K`. -/
theorem toposModuleBaseChangeMap_app_eq (comm : g' ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (toposModuleBaseChangeMap f g f' g' comm).app K =
      (modulePullback B S hS g).map ((modulePushforwardIso B S hS f).hom.app K) ≫
        (moduleBaseChangeMap f g f' g' comm).app K ≫
        (modulePushforwardIso B S hS f').inv.app ((modulePullback B S hS g').obj K) := by
  rw [toposModuleBaseChangeMap_eq_moduleBaseChangeMap f g f' g' comm]
  rfl

end Square

/-- **The degree-zero clause of Stacks 073K, part (1), at the ringed-topoi spelling of the direct
image.**  For a cartesian square of algebraic spaces whose base `g` is flat and whose right
morphism `f` is quasi-compact and quasi-separated, the degree-zero base change map
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` is an isomorphism at every quasi-coherent
`𝒪_X`-module.

This is `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat` carried
across `AlgebraicGeometry.Space.toposModuleBaseChangeMap_app_eq`;  the two maps differ by two
components of `AlgebraicGeometry.Space.modulePushforwardIso`, so no part of the chart computation
is repeated.

It is the degree-zero base change map that the base change map of **Stacks 0736** on `D⁺`
descends from, and so is the spelling at which the reduction of part (1) consumes the degree-zero
case.  It is **not** part (1), which quantifies over all `i ≥ 0`;  see the implementation notes of
this file for the one step still missing between this and degree zero of the map of higher direct
images. -/
theorem isIso_toposModuleBaseChangeMap_app_of_isFlat {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    IsIso ((toposModuleBaseChangeMap f g f' g' sq.w).app F) := by
  have := isIso_moduleBaseChangeMap_app_of_isFlat sq hfqc hfqs hg F hF
  rw [toposModuleBaseChangeMap_app_eq f g f' g' sq.w F]
  exact ((modulePullback B S hS g).mapIso ((modulePushforwardIso B S hS f).app F) ≪≫
    asIso ((moduleBaseChangeMap f g f' g' sq.w).app F) ≪≫
    ((modulePushforwardIso B S hS f').app
      ((modulePullback B S hS g').obj F)).symm).isIso_hom

end AlgebraicGeometry.Space

end
