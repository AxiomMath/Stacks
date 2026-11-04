module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueing

/-!
# Base change of the chart restriction of a module along a morphism of algebraic spaces

Let `a : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `V`
be an étale scheme chart of `Z` and `W` an étale scheme chart of `X`, and let `g` be a morphism
of the underlying objects of the site which commutes with the two chart structure morphisms
through `a`.  Restricting an `𝒪_Z`-module to `V` and pulling back along `g` then agrees with
pulling back along `a` and restricting to `W`.  This file proves that compatibility in the
inverse-image reading of the chart restriction, that is for
`AlgebraicGeometry.Space.chartModuleRestriction`, where it is a consequence of the composition
comparison of Stacks 03LU alone: no quasi-coherence, no étaleness and no cartesianness of the
square is used.

## Main definitions

* `AlgebraicGeometry.Space.chartSpaceMapOver` is the morphism of represented algebraic spaces
  attached to a morphism of the underlying objects of an étale chart of `X` and an étale chart
  of `Z`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCommSquareIso`: for a *commuting* square of algebraic
  spaces, the two composites of inverse images of modules around it are isomorphic.
* `AlgebraicGeometry.Space.chartSpaceMapOver_comp_chartToSpace`: a morphism of chart schemes
  which commutes with the structure morphisms through `a` represents a morphism of algebraic
  spaces over `a`.
* `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`: the base-change compatibility
  of the chart restriction of modules, in the inverse-image reading, and
  `AlgebraicGeometry.Space.chartModuleRestrictionBaseChange`, the same statement written in the
  shape of `AlgebraicGeometry.Space.ChartRestrictionBaseChange`.
* `AlgebraicGeometry.Space.modulePullbackCommSquareIso_eq`,
  `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app` and
  `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso_eq`: the two comparisons written
  out as composites, and the composite's value on a single module split into its three factors.
* `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` and
  `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso_hom_app`: the same three factors
  with the middle one read as the transport of the single object `(modulePullback _).obj G`
  along the commutation of the square, which is the shape a consumer wants.
* `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_val_app` and
  `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso_hom_app_val_app`: **the two
  comparisons read on a section**, the middle factor being the transport of the module of
  sections.  This is what a consumer computing with the comparison works with, and it leaves
  nothing about the square unevaluated: only the composition comparison of Stacks 03LU itself
  remains.  The implementation note on `modulePullbackCommSquareIso_hom_app_eqToHom` records
  what the kernel will and will not do with these transports.

## Implementation notes

`AlgebraicGeometry.Space.modulePullbackSquareIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardEtaleBaseChange.lean` is the same
comparison for a square assumed *cartesian*, and its implementation notes record that only the
commutation of the square is consumed.  The commuting-square form is what a square of étale
charts over a morphism needs, since such a square is not cartesian: the two charts are chosen
independently.  Both are the mate of the composition comparison and neither is derived from the
other here, so that no pre-existing module acquires an import.

The comparison is stated as an isomorphism of functors rather than of modules so that it can be
transported along further natural transformations; the base change of a single module is the
component of this isomorphism, and
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` is stated in the direction in
which `AlgebraicGeometry.Space.ChartRestrictionBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/ModuleFiniteness.lean` is stated.

This is *not* `AlgebraicGeometry.Space.ChartRestrictionBaseChange`, which is the same
compatibility for the Zariski reading `AlgebraicGeometry.Space.restrictToChart` of the chart
restriction — a sheaf of modules on the chart scheme — and takes the pullback inside the
schemes.  What separates the two is no longer anything about the square: it is the comparison
of the small étale and the Zariski descriptions of a module, in the two square-free forms

* the identification, at a single étale chart, of `AlgebraicGeometry.Space.restrictToChart`
  with the Zariski reading of `AlgebraicGeometry.Space.chartModuleRestriction`, and
* the compatibility of that Zariski reading with pullback along a single morphism of the
  underlying schemes of two charts,

both of which are instances of the equivalence clause of Descent, Proposition 03DX(2).  What is
shown here is that the square itself costs nothing, so a comparison indexed by charts and by
morphisms of chart schemes is all that the square-indexed statement can still be asking for.

Those two forms are now available — the first as
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` together with
`AlgebraicGeometry.Space.restrictToChartSchemeIsoIdEtaleChart`, the second as
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` — and
together with the comparison of this file they do suffice:
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` proves
`AlgebraicGeometry.Space.ChartRestrictionBaseChange`, consuming
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` below for the square.  Both forms
need the module to be quasi-coherent, which is where the clause of 03DX(2) enters; it is carried
in this development as
`AlgebraicGeometry.Space.QuasicoherentIsEssImageAssociatedModule` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean`, and the
route taken does not need it, the counit of the associated-module adjunction being an
isomorphism at a quasi-coherent module.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images of modules around a commuting square -/

/-- **Inverse images of modules around a commuting square of algebraic spaces.** For a square
`γ ≫ cZ = cX ≫ a` of morphisms of algebraic spaces, restricting along `cZ` and pulling back
along `γ` agrees with pulling back along `a` and restricting along `cX`.

Both composites are the inverse image along the diagonal of the square, by the composition
comparison of Stacks 03LU; the square enters only through its commutation. -/
def modulePullbackCommSquareIso {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'}
    {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a) :
    modulePullback B S hS cZ ⋙ modulePullback B S hS γ ≅
      modulePullback B S hS a ⋙ modulePullback B S hS cX :=
  modulePullbackCompIso B S hS γ cZ ≪≫
    eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq) ≪≫
      (modulePullbackCompIso B S hS cX a).symm

/-- The last two factors of `AlgebraicGeometry.Space.modulePullbackCommSquareIso` on a single
module. -/
theorem modulePullbackCommSquareIso_hom_app_tail {X X' Z' Z : AlgebraicSpaces B S hS}
    {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq) ≪≫
        (modulePullbackCompIso B S hS cX a).symm).hom.app G =
      (eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq)).hom.app G ≫
        (modulePullbackCompIso B S hS cX a).inv.app G :=
  rfl

/-- **The comparison around a commuting square, on a single module, decomposed into its three
factors.**  The two outer factors are `AlgebraicGeometry.Space.modulePullbackCompIso` on the
module; the middle one is the transport along the commutation of the square, left as the
component of the transport of functors.

`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` is the same decomposition
with the middle factor turned into the transport of the single object `(modulePullback _).obj G`,
which is the shape a consumer wants; the implementation note there records what the kernel will
and will not do with these transports.  Decomposing the composition, by contrast, costs nothing:
that is this lemma and `modulePullbackCommSquareIso_hom_app_tail`, both of which are only
`CategoryTheory.NatTrans.comp_app`. -/
theorem modulePullbackCommSquareIso_eq {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'}
    {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a) :
    modulePullbackCommSquareIso B S hS hsq =
      modulePullbackCompIso B S hS γ cZ ≪≫
        eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq) ≪≫
          (modulePullbackCompIso B S hS cX a).symm :=
  rfl

/-- The component at a module `G` of the composite of
`AlgebraicGeometry.Space.modulePullbackCompIso` for `γ` and `cZ`, the transport along the
commutation of the square, and the inverse of `AlgebraicGeometry.Space.modulePullbackCompIso` for
`cX` and `a`, is the composite of the three components at `G`. -/
theorem modulePullbackCommSquareIso_hom_app {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'}
    {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackCompIso B S hS γ cZ ≪≫
          eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq) ≪≫
            (modulePullbackCompIso B S hS cX a).symm).hom.app G =
      (modulePullbackCompIso B S hS γ cZ).hom.app G ≫
        ((eqToIso (congrArg (fun k ↦ modulePullback B S hS k) hsq)).hom.app G ≫
          (modulePullbackCompIso B S hS cX a).inv.app G) :=
  rfl

/-! ### The comparison on a module and on a section -/

/-- **A composite of three morphisms of `𝒪`-modules, read on a section.**

Stated at the categories `AlgebraicGeometry.Space.Modules` themselves and with the three factors
arbitrary, which is the only shape in which it is affordable.  The same `rfl` is free at an
arbitrary site as well, but *instantiating* that version at the comparison below is not: the
category instance it carries is assembled from the site and the structure ring sheaf by its own
route, and reconciling it with the one the goal carries makes the kernel compare two
`AlgebraicGeometry.Space.modulePullback`-objects, which is the one question that does not
terminate (see the implementation note on
`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom`).  Here every instance
matches on the nose and the lemma is pure substitution. -/
theorem comp_comp_val_app_apply {X' : AlgebraicSpaces B S hS}
    {A A' A'' A''' : Modules.{u, u} B S hS X'.1 X'.2}
    (φ : A ⟶ A') (ψ : A' ⟶ A'') (χ : A'' ⟶ A''') (T : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : A.val.obj T) :
    (φ ≫ ψ ≫ χ).val.app T s = χ.val.app T (ψ.val.app T (φ.val.app T s)) :=
  rfl

/-- **The transport of the inverse image of modules along an equality of morphisms, on a single
module.**  The two functors compared are one and the same
`AlgebraicGeometry.Space.modulePullback` at two equal arguments, so the transport of functors
becomes the transport of the single object `(modulePullback _).obj G`, which is the shape a
consumer wants.

This is the pullback-side analogue of `RingedSpaceModuleAdjunction.modulePullbackCongr_hom_app`,
and like it the proof substitutes the equality of morphisms rather than reducing the transport:
the two morphisms are variables here, so after the substitution both sides are the identity and
nothing about `modulePullback` has to be unfolded.  At the use site the equality of morphisms is
no longer substitutable — in
`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` it is the commutation of a
square — and instantiating this lemma there costs nothing. -/
theorem modulePullback_eqToIso_hom_app {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y} (h : f = g)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (eqToIso (congrArg (fun k ↦ modulePullback B S hS k) h)).hom.app G =
      eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) h) := by
  subst h
  rfl

/-- **The transport of the inverse image of modules along an equality of morphisms, on a
section.**  It is the transport of the module of sections, the two morphisms having the same
inverse image.

Proved by substituting the equality of morphisms, for the reason recorded on
`AlgebraicGeometry.Space.modulePullback_eqToIso_hom_app`; this is the step that makes the
comparison readable on a section at all, since projecting the underlying map of presheaves out
of the transport itself is exactly the question the kernel cannot answer. -/
theorem modulePullback_eqToHom_val_app_apply {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y}
    (h : f = g) (G : Modules.{u, u} B S hS Y.1 Y.2) (T : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : ((modulePullback B S hS f).obj G).val.obj T) :
    (eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) h)).val.app T s =
      eqToHom (congrArg (fun k ↦ ((modulePullback B S hS k).obj G).val.obj T) h) s := by
  subst h
  rfl

/-- **The comparison around a commuting square, on a single module, with the middle factor read
as a transport of objects.**  The two outer factors are
`AlgebraicGeometry.Space.modulePullbackCompIso` on the module and the middle one is the
transport of `(modulePullback _).obj G` along the commutation of the square.  This is the form a
consumer reading the comparison on a module works with.

*What the kernel will and will not do with these transports.*  The transport in
`AlgebraicGeometry.Space.modulePullbackCommSquareIso` is along an equality of *morphisms of
algebraic spaces*, so `CategoryTheory.eqToHom_app` turns it into the transport of a single
object.  That step is affordable, but only when it is asked on its own: asking it of the
`CategoryTheory.eqToIso` spelling in one step — `eqToHom_app` elaborated directly against a goal
whose left-hand side is `(eqToIso _).hom.app G` — exhausts the kernel's deterministic budget,
while the same goal split into `CategoryTheory.eqToIso.hom` and then `eqToHom_app`, or proved by
substituting the equality of morphisms as
`AlgebraicGeometry.Space.modulePullback_eqToIso_hom_app` does, costs nothing.  So the budget is
not spent on the transport as such; it is spent whenever a *single* `isDefEq` has to bridge two
differences at once, and the remedy throughout is an explicit `Eq.trans` through the intermediate
spelling.

What is genuinely out of reach is one atomic question, which no splitting reaches: projecting the
underlying map of presheaves out of the transport, `(eqToHom _).val`.  `eqToHom` is
`Eq.mpr`-based, so reducing it to a constructor — which the projection demands — means deciding
`(modulePullback (γ ≫ cZ)).obj G = (modulePullback (cX ≫ a)).obj G`, and
`AlgebraicGeometry.Space.modulePullback` is `pullbackModules` of the morphism of ringed topoi,
hence a sheafification; the two sheafifications are at two *different* morphisms, so there is no
structural shortcut and the kernel unfolds both.  The same `rfl` with the middle factor left
abstract is free (`AlgebraicGeometry.Space.comp_comp_val_app_apply`), which is what locates the
cost, and `AlgebraicGeometry.Space.modulePullback_eqToHom_val_app_apply` avoids the question
altogether by substituting the equality of morphisms before the projection is asked for. -/
theorem modulePullbackCommSquareIso_hom_app_eqToHom {X' X Z' Z : AlgebraicSpaces B S hS}
    {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackCommSquareIso B S hS hsq).hom.app G =
      (modulePullbackCompIso B S hS γ cZ).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hsq) ≫
          (modulePullbackCompIso B S hS cX a).inv.app G := by
  rw [modulePullbackCommSquareIso_eq B S hS hsq,
    modulePullbackCommSquareIso_hom_app B S hS hsq G,
    modulePullback_eqToIso_hom_app B S hS hsq G]

/-- The comparison around a commuting square on a section, still written as the composite of its
three factors.  One `congrArg` of
`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom`; it is its own declaration
because the deterministic budget is per declaration. -/
private theorem modulePullbackCommSquareIso_hom_app_val_app_composite
    {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z}
    (hsq : γ ≫ cZ = cX ≫ a) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (T : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : ((modulePullback B S hS cZ ⋙ modulePullback B S hS γ).obj G).val.obj T) :
    ((modulePullbackCommSquareIso B S hS hsq).hom.app G).val.app T s =
      ((modulePullbackCompIso B S hS γ cZ).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hsq) ≫
          (modulePullbackCompIso B S hS cX a).inv.app G).val.app T s :=
  congrArg (fun m ↦ m.val.app T s) (modulePullbackCommSquareIso_hom_app_eqToHom B S hS hsq G)

/-- The composite of the three factors, on a section, read one factor at a time.
`AlgebraicGeometry.Space.comp_comp_val_app_apply` instantiated at them. -/
private theorem modulePullbackCommSquareIso_hom_app_val_app_split
    {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z}
    (hsq : γ ≫ cZ = cX ≫ a) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (T : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : ((modulePullback B S hS cZ ⋙ modulePullback B S hS γ).obj G).val.obj T) :
    ((modulePullbackCompIso B S hS γ cZ).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hsq) ≫
          (modulePullbackCompIso B S hS cX a).inv.app G).val.app T s =
      ((modulePullbackCompIso B S hS cX a).inv.app G).val.app T
        ((eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hsq)).val.app T
          (((modulePullbackCompIso B S hS γ cZ).hom.app G).val.app T s)) :=
  comp_comp_val_app_apply B S hS ((modulePullbackCompIso B S hS γ cZ).hom.app G)
    (eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hsq))
    ((modulePullbackCompIso B S hS cX a).inv.app G) T s

/-- **The comparison of inverse images of modules around a commuting square, on a section.**  For
a section of the inverse image along `γ` of the restriction along `cZ` of a module, over an
object of the small étale site of the corner `X'`, the comparison acts by the composition
comparison of Stacks 03LU along `γ` and `cZ`, then the transport of the module of sections along
the commutation of the square, then the inverse of the composition comparison along `cX` and `a`.

Only the composition comparison of Stacks 03LU is left unevaluated; everything the square itself
contributes is discharged here.  The three factors are read off one at a time, through
`AlgebraicGeometry.Space.comp_comp_val_app_apply` and
`AlgebraicGeometry.Space.modulePullback_eqToHom_val_app_apply`, for the reasons recorded on
`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom`. -/
theorem modulePullbackCommSquareIso_hom_app_val_app {X' X Z' Z : AlgebraicSpaces B S hS}
    {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (T : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : ((modulePullback B S hS cZ ⋙ modulePullback B S hS γ).obj G).val.obj T) :
    ((modulePullbackCommSquareIso B S hS hsq).hom.app G).val.app T s =
      ((modulePullbackCompIso B S hS cX a).inv.app G).val.app T
        (eqToHom (congrArg (fun k ↦ ((modulePullback B S hS k).obj G).val.obj T) hsq)
          (((modulePullbackCompIso B S hS γ cZ).hom.app G).val.app T s)) :=
  ((modulePullbackCommSquareIso_hom_app_val_app_composite B S hS hsq G T s).trans
      (modulePullbackCommSquareIso_hom_app_val_app_split B S hS hsq G T s)).trans
    (congrArg (fun x ↦ ((modulePullbackCompIso B S hS cX a).inv.app G).val.app T x)
      (modulePullback_eqToHom_val_app_apply B S hS hsq G T
        (((modulePullbackCompIso B S hS γ cZ).hom.app G).val.app T s)))

/-! ### Squares of étale scheme charts over a morphism of algebraic spaces -/

variable {X Z : AlgebraicSpaces B S hS}

/-- The morphism of represented algebraic spaces attached to a morphism of the underlying
objects of the site of an étale chart `W` of `X` and an étale chart `V` of `Z`. -/
def chartSpaceMapOver {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left) :
    chartSpace B S hS X W ⟶ chartSpace B S hS Z V :=
  ObjectProperty.homMk (yoneda.map g)

/-- A morphism of the underlying objects of two étale charts which commutes with their
structure morphisms through `a` represents a morphism of algebraic spaces over `a`. -/
theorem chartSpaceMapOver_comp_chartToSpace (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    chartSpaceMapOver B S hS g ≫ chartToSpace B S hS Z V =
      chartToSpace B S hS X W ≫ a :=
  ObjectProperty.hom_ext _ hg

/-- **The base-change compatibility of the chart restriction of modules, in the inverse-image
reading.** For a morphism `a : X ⟶ Z` of algebraic spaces, an étale chart `V` of `Z` and an
étale chart `W` of `X` joined by a morphism `g` of the underlying objects of the site over `a`,
the inverse image along `g` of the restriction of an `𝒪_Z`-module to `V` is the restriction to
`W` of its inverse image along `a`.

No quasi-coherence of the module is needed, and the square of charts is not assumed cartesian:
this is the composition comparison of Stacks 03LU and nothing else. -/
def chartModuleRestrictionBaseChangeIso (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    chartModuleRestriction B S hS Z V ⋙
        modulePullback B S hS (chartSpaceMapOver B S hS g) ≅
      modulePullback B S hS a ⋙ chartModuleRestriction B S hS X W :=
  modulePullbackCommSquareIso B S hS
    (chartSpaceMapOver_comp_chartToSpace B S hS a g hg)

/-- **The base-change compatibility of the chart restriction, written out as the composition
comparison of Stacks 03LU twice over and the commutation of the square.**

This together with `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app` is the reading
of the comparison on a single module, and hence on a section: rewriting with this equation
replaces the name by the composite, which the kernel can then decompose, and that lemma splits
the composite into its three factors.  Going directly from the name to the three factors in one
step is what the kernel declines; see the implementation note on
`modulePullbackCommSquareIso_hom_app`. -/
theorem chartModuleRestrictionBaseChangeIso_eq (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    chartModuleRestrictionBaseChangeIso B S hS a g hg =
      modulePullbackCompIso B S hS (chartSpaceMapOver B S hS g)
          (chartToSpace B S hS Z V) ≪≫
        eqToIso (congrArg (fun k ↦ modulePullback B S hS k)
            (chartSpaceMapOver_comp_chartToSpace B S hS a g hg)) ≪≫
          (modulePullbackCompIso B S hS (chartToSpace B S hS X W) a).symm :=
  rfl

/-- The base-change compatibility of the chart restriction, on a module, is the
commuting-square comparison at the square of the two charts.  The chart restriction is the
inverse image along the structure morphism of the chart on the nose, so this is a `rfl`; it is
its own declaration so that the kernel is never asked to take that step and decompose the
comparison at once. -/
theorem chartModuleRestrictionBaseChangeIso_hom_app_eq_commSquare (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (chartModuleRestrictionBaseChangeIso B S hS a g hg).hom.app G =
      (modulePullbackCommSquareIso B S hS
        (chartSpaceMapOver_comp_chartToSpace B S hS a g hg)).hom.app G :=
  rfl

/-- **The base-change compatibility of the chart restriction, on a single module, decomposed
into its three factors.**  The two outer factors are the composition comparison of Stacks 03LU,
and the middle one is the transport of `(modulePullback _).obj G` along the commutation of the
square of charts.

This is `AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` at the square of
`AlgebraicGeometry.Space.chartSpaceMapOver_comp_chartToSpace`, reached through
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso_hom_app_eq_commSquare` rather than
in one step: applying that lemma directly here asks the kernel to unfold
`AlgebraicGeometry.Space.chartModuleRestriction` and decompose the comparison in a single
`isDefEq`, which exhausts its budget, whereas each half on its own is free. -/
theorem chartModuleRestrictionBaseChangeIso_hom_app (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    (chartModuleRestrictionBaseChangeIso B S hS a g hg).hom.app G =
      (modulePullbackCompIso B S hS (chartSpaceMapOver B S hS g)
          (chartToSpace B S hS Z V)).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj G)
            (chartSpaceMapOver_comp_chartToSpace B S hS a g hg)) ≫
          (modulePullbackCompIso B S hS (chartToSpace B S hS X W) a).inv.app G :=
  (chartModuleRestrictionBaseChangeIso_hom_app_eq_commSquare B S hS a g hg G).trans
    (modulePullbackCommSquareIso_hom_app_eqToHom B S hS
      (chartSpaceMapOver_comp_chartToSpace B S hS a g hg) G)

/-- **The base-change compatibility of the chart restriction of modules, read on a section.**
For a section, over an object of the small étale site of the chart space of `W`, of the inverse
image along `g` of the restriction of `G` to `V`, the comparison acts by the composition
comparison of Stacks 03LU along `g` and the structure morphism of `V`, then the transport of the
module of sections along the commutation of the square of charts, then the inverse of the
composition comparison along the structure morphism of `W` and `a`.

This is the form a consumer computing with the comparison needs, and it is what the transport
along the commutation of the square made unreachable;
`AlgebraicGeometry.Space.modulePullbackCommSquareIso_hom_app_eqToHom` records the measurement.
Nothing about the square is left unevaluated: what remains is the composition comparison of
Stacks 03LU itself, which is `CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions
and is determined by `AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom`
rather than by anything in this file. -/
theorem chartModuleRestrictionBaseChangeIso_hom_app_val_app (a : X ⟶ Z)
    {V : SmallEtale B S hS Z.obj} {W : SmallEtale B S hS X.obj}
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2)
    (T : (SmallEtale B S hS (chartSpace B S hS X W).1)ᵒᵖ)
    (s : ((chartModuleRestriction B S hS Z V ⋙
      modulePullback B S hS (chartSpaceMapOver B S hS g)).obj G).val.obj T) :
    ((chartModuleRestrictionBaseChangeIso B S hS a g hg).hom.app G).val.app T s =
      ((modulePullbackCompIso B S hS (chartToSpace B S hS X W) a).inv.app G).val.app T
        (eqToHom (congrArg (fun k ↦ ((modulePullback B S hS k).obj G).val.obj T)
            (chartSpaceMapOver_comp_chartToSpace B S hS a g hg))
          (((modulePullbackCompIso B S hS (chartSpaceMapOver B S hS g)
              (chartToSpace B S hS Z V)).hom.app G).val.app T s)) :=
  (congrArg (fun m ↦ m.val.app T s)
      (chartModuleRestrictionBaseChangeIso_hom_app_eq_commSquare B S hS a g hg G)).trans
    (modulePullbackCommSquareIso_hom_app_val_app B S hS
      (chartSpaceMapOver_comp_chartToSpace B S hS a g hg) G T s)

/-- **The base-change compatibility of the chart restriction, written in the shape of
`AlgebraicGeometry.Space.ChartRestrictionBaseChange`.** The two differ in the reading of the
chart restriction and of the pullback: here the restriction to a chart is the inverse image of
modules along the represented morphism of algebraic spaces and the base change is taken along
the represented morphism as well, whereas
`AlgebraicGeometry.Space.ChartRestrictionBaseChange` reads the restriction as a sheaf of
modules on the chart scheme and takes the base change inside the schemes.

In this reading the comparison is constructed rather than assumed, and the quasi-coherence of
the module, which the Zariski form asks for, is not needed. -/
def chartModuleRestrictionBaseChange :
    ∀ {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
      (G : Modules.{u, u} B S hS Z.obj Z.property)
      (V : SmallEtale B S hS Z.obj) (W : SmallEtale B S hS X.obj)
      (g : W.obj.left ⟶ V.obj.left),
      yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom →
      ((modulePullback B S hS (chartSpaceMapOver B S hS g)).obj
          ((chartModuleRestriction B S hS Z V).obj G) ≅
        (chartModuleRestriction B S hS X W).obj ((modulePullback B S hS a).obj G)) :=
  fun a G _ _ g hg ↦ (chartModuleRestrictionBaseChangeIso B S hS a g hg).app G

end AlgebraicGeometry.Space

end
