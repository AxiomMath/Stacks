module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRepresentedNaturality
public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackComposition
public import StacksFrontier.CategoryTheory.SquareTransportConormal

/-!
# The transport of the inverse image carries the ringed-space square comparison to the spaces one

Let
```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B`.  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` identifies the inverse
image of `𝒪`-modules of [Stacks Project, Tag 03LU] along a represented morphism, read at the
`𝒪`-module of an associated module, with the `𝒪`-module of the Zariski pullback along the
underlying morphism of schemes.  This file proves that **that identification carries the
ringed-space square comparison `Stacks.ClosedImmersion.pullbackCompIso` to the spaces-side square
comparison `AlgebraicGeometry.Space.squarePullbackCompIso`**, read at
`Stacks.ClosedImmersion.idealSheaf` of `j'`.

That is the hypothesis `hΞ` of
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedNaturality.lean`, so the
naturality
of part (1) of [Stacks Project, Tag 04G2] in the closed immersion is unconditional from here; it
is restated as such below.

## Main results

* `AlgebraicGeometry.Space.pullbackCompIso_hom_eq_pullbackComp`: **the ringed-space square
  comparison is the two Zariski composition comparisons of Mathlib with the transport along the
  commutativity of the square between them** — true by `rfl`, see the implementation notes.
* `AlgebraicGeometry.Space.pullbackComp_comp_eqToHom`: the same, solved for the transport.  This
  is the second of the three residual steps the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleObjPullbackComposition.lean` list
  between the composition law and `hΞ`.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_eqToHom` and
  `AlgebraicGeometry.Space.eqToHom_app_representedSpaceMap_square`: the **first** of those three
  steps — the transport of the law's right-hand side along the commutativity of the square,
  obtained by `subst` at plain variables of the site, and the respelling of the spaces-side
  transport that it meets.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_eq`: the composition
  law with its third factor taken as a variable, which is the **third** step — matching that
  factor.

## Main results, continued

* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_squarePullbackCompIso`: **the
  hypothesis `hΞ` itself**, proved.
* `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`: the
  naturality of part (1) of [Stacks Project, Tag 04G2] in the closed immersion, with nothing
  assumed.

## The kernel obstruction, and how it is avoided

`hΞ` elaborates in about forty seconds, and assembled naively it is a **kernel** deterministic
timeout.  The diagnosis is written out here; every claim below was checked in a module of its
own.

### The rule

> A morphism named by two statements in two definitionally equal but syntactically
> different spellings may be shared between two hypotheses of one application **only when it
> occurs as one side of an `Eq`**.  Inside a composite the kernel unfolds
> `CategoryTheory.CategoryStruct.comp` and reaches for `AlgebraicGeometry.Space.modulePullback` —
> a left adjoint built by sheafification — and the share is a deterministic timeout.

Both halves are checked directly.  The transport along the commutativity of the square of
represented
spaces, spelled `representedSpaceMap b ≫ representedSpaceMap j'` on the reading's side and
`representedSpaceMap (b ≫ j')` on the transport identity's, satisfies
`eqToHom e₁ = eqToHom e₂` by **`rfl`, free**, as a goal on its own; the two **objects** it runs
between are equal by `rfl`, also free.  But forcing the reading and the transport identity to
share that transport — or to share either of its endpoint objects, which brings the transport
with them — is a kernel deterministic timeout, in either order of the two hypotheses.  The
earlier record that "reconciling the two spellings is free at the level of the objects" is true
of a bare object equation and false of a share, and it was the share that blocked the
instantiation.

### The three devices that remove it

* the middle transport is **never shared**: it is removed from every composite by
  `Stacks.CategoryTheory.mid_eq_of_reading`, which solves the reading for it, after which every
  remaining hypothesis is transport-free;
* the transport `δ` of the inner objects, which the transport identity and
  `Stacks.CategoryTheory.map_map_comp_eqToHom` spell differently, is **taken twice** by
  `Stacks.CategoryTheory.square_transport_aux_of_mid`, with `rfl` between the two spellings;
* the two transports whose spelling `hΞ`'s own statement fixes — the one at `b` read at
  `Stacks.ClosedImmersion.conormalSheaf` rather than at the pulled-back ideal sheaf, and the one
  at `j` read at the pulled-back ideal sheaf — are **supplied** to
  `Stacks.CategoryTheory.comp₃_mid_eq_of` and `Stacks.CategoryTheory.cancel_left_of_comp₃`
  instead of being inherited from the two composition laws.

With those three in place the assembly is **two applications**, not one, and both are free: the
hypothesis sets of `Stacks.CategoryTheory.square_transport_aux_of_mid` and of
`Stacks.CategoryTheory.eq_of_comp_cancel_right` were each checked on their own.  A single
application holding all of them is a kernel deterministic timeout even with every share removed,
so the split is necessary too.

### Further elaboration facts, each checked by its own declaration

* `Stacks.ClosedImmersion.conormalSheaf` of `j'` **is** the Zariski pullback along `j'` of
  `Stacks.ClosedImmersion.idealSheaf` of `j'` by `rfl`, and the kernel takes it — but only
  because the transport read at it is supplied rather than shared;
* the respelled reading must **not** be proved by
  `rw [squarePullbackCompIso_hom_app, eqToHom_app]`: that is a kernel deterministic timeout at
  77 s **even with the four spaces and the four morphisms of the square variables**, because the
  rewrite's closing `rfl` compares the two `eqToHom` terms with the middle factor still in the
  motive.  Four other routes are free, all four in one 3.3 s module; see
  `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_eqToHom`.  That
  `Stacks.CategoryTheory.reading_eqToHom` applied to
  `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app` is a kernel timeout holds at the
  geometric **instantiation** and not at variables, which is what makes a respelling possible at
  all;
* the equation `(eqToHom e₁).app M = (eqToHom e₂).app M` between the two spellings of the
  transport is a kernel deterministic timeout even at a **variable** module, while the same
  equation with `CategoryTheory.eqToHom_app` rewritten on the left is free (0.2 s);
* the two cancellations `F.map e.inv ≫ F.map e.hom = 𝟙 _` cannot be proved here by
  `rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]`: `rw` reports that it cannot find
  `CategoryTheory.Functor.map ?F ?f ≫ CategoryTheory.Functor.map ?F ?g` in a goal that displays
  exactly that.  `Stacks.CategoryTheory.map_inv_comp_map_hom` is what is used;
* taking the invertible morphisms as pairs with their cancellations rather than as
  `CategoryTheory.Iso`s is necessary, and taking them as an `Iso` is actively worse: a generic
  lemma stating the composition law at `e.hom` for an `Iso` variable `e` is a kernel
  deterministic timeout where the same lemma at a morphism variable is free;
* reordering the hypotheses so the shared objects are read off the transport identity, taking the
  two composition comparisons of the inner category as variables, naming the ideal sheaf, and
  `attribute [local irreducible]` on six definitions were each tested: all are necessary for
  the **elaborator** (without them the assembly is a 200 000-heartbeat `isDefEq` or `whnf`
  timeout) and none of them moves the kernel;
* reconciling the two spellings of the square's composite is free at the level of
  `AlgebraicGeometry.Scheme.Modules` and costs about thirty seconds under the associated-module
  functor and the identification of the sites, which is why
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_eq` pays it once at
  plain variables.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso squarePullbackCompIso
  representedSmallEtaleModuleEquivalence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')

section Law

variable {T₁ T₂ T₃ : BigFppfOver B S hS}

/-- **The composition law for the transport of the inverse image, with its third factor taken as
a variable.**

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp` states the law with its
third factor written out as the associated module of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, so the equation's type is fixed at the spelling
in which the composite of the square's two routes is a *composite of morphisms of schemes*.  The
transports of the law's right-hand side are at the spelling in which that composite is the image
of a *composite of morphisms of the site*.  Reconciling the two is free at plain variables and
costs about thirty seconds under the associated-module functor and the identification of the
sites at a geometric instantiation, so it is paid here, once, and nothing above this pays it: a
consumer passes `k` as `_` with `hk := rfl`.

This is the strongest form of the rule that a generic statement should be instantiated rather
than restated — Lean does not recheck a proved statement's internal definitional equalities. -/
theorem representedAssociatedModulePullbackIso_comp_of_eq (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (hp : yoneda.relativelyRepresentable (yoneda.map p))
    (hq : yoneda.relativelyRepresentable (yoneda.map q))
    (hpq : yoneda.relativelyRepresentable (yoneda.map (p ≫ q)))
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₃).Modules)
    (k : (representedSmallEtaleModuleEquivalence B S hS T₁).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).obj
            ((Scheme.Modules.pullback (B.inclusion.map p.left)).obj
              ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕))) ⟶
        (representedSmallEtaleModuleEquivalence B S hS T₁).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).obj
            ((Scheme.Modules.pullback (B.inclusion.map (p ≫ q).left)).obj 𝓕)))
    (hk : k = (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).map
        ((Scheme.Modules.pullbackComp (B.inclusion.map p.left)
          (B.inclusion.map q.left)).hom.app 𝓕))) :
    (modulePullback B S hS (representedSpaceMap B S hS p)).map
          (representedAssociatedModulePullbackIso B S hS q hq 𝓕).hom ≫
        (representedAssociatedModulePullbackIso B S hS p hp
          ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕)).hom ≫ k =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T₃).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)) ≫
        (representedAssociatedModulePullbackIso B S hS (p ≫ q) hpq 𝓕).hom := by
  subst hk
  exact representedAssociatedModulePullbackIso_comp B S hS p q hp hq hpq 𝓕

end Law

/-- **The ringed-space square comparison of a commutative square of the big fppf category is the
two Zariski composition comparisons with the transport along the commutativity of the square
between them.**

True by `rfl`: `Stacks.ClosedImmersion.pullbackCompIso` is built from
`RingedSpaceModuleAdjunction.modulePullbackComp` on each side and
`RingedSpaceModuleAdjunction.modulePullbackCongr` in the middle, and the first of those is
`CategoryTheory.SheafOfModules.pullbackComp` of the structure-sheaf maps, which is what
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is too. -/
theorem pullbackCompIso_hom_eq_pullbackComp (hsq : j ≫ a = b ≫ j') :
    (Stacks.ClosedImmersion.pullbackCompIso
        (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
        (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
        (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
        (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
        (toShHom_square_of_comp_eq B S hS j j' b a hsq)
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom =
      (Scheme.Modules.pullbackComp (B.inclusion.map b.left)
            (B.inclusion.map j'.left)).hom.app
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
        (eqToHom (congrArg
            (fun m : ((BigFppfOver.toScheme B S hS).obj R).toLocallyRingedSpace.toRingedSpace ⟶
                ((BigFppfOver.toScheme B S hS).obj V').toLocallyRingedSpace.toRingedSpace =>
              RingedSpaceModuleAdjunction.modulePullback m)
            (toShHom_square_of_comp_eq B S hS j j' b a hsq).symm)).app
            (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map j.left)
              (B.inclusion.map a.left)).inv.app
            (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :=
  rfl

/-- The middle factor of `AlgebraicGeometry.Space.pullbackCompIso_hom_eq_pullbackComp`, read at
the ideal sheaf: the transport of the pullback functors along the commutativity of the square of
ringed spaces is the transport of the two pulled-back ideal sheaves.

The target transport is taken along an equality supplied as a hypothesis rather than formed from
the commutativity of the square of the site, so that no statement here mentions both spellings of
the composite; see the implementation notes. -/
theorem pullbackCompIso_eqToHom_app_eq (hsq : j ≫ a = b ≫ j')
    (hA : (Scheme.Modules.pullback (B.inclusion.map (b ≫ j').left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) =
        (Scheme.Modules.pullback (B.inclusion.map (j ≫ a).left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)) :
    (eqToHom (congrArg
          (fun m : ((BigFppfOver.toScheme B S hS).obj R).toLocallyRingedSpace.toRingedSpace ⟶
              ((BigFppfOver.toScheme B S hS).obj V').toLocallyRingedSpace.toRingedSpace =>
            RingedSpaceModuleAdjunction.modulePullback m)
          (toShHom_square_of_comp_eq B S hS j j' b a hsq).symm)).app
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) =
      eqToHom hA := by
  rw [eqToHom_app]
  rfl

/-- **The ringed-space square comparison, solved for the transport.**  The composition comparison
of the route `b` then `j'`, followed by the transport of the two pulled-back ideal sheaves, is the
ringed-space square comparison followed by the composition comparison of the route `j` then `a`.

This is `AlgebraicGeometry.Space.pullbackCompIso_hom_eq_pullbackComp` with the third factor
cancelled, and it is the shape `Stacks.CategoryTheory.map_map_comp_eqToHom` consumes.

The two composition comparisons are taken as **variables `u` and `v` with their identifications
`hu` and `hv`**, rather than written into the statement.  That fixes the two middle objects of
the composites at the spelling in which the composite of the square's two routes is the image of
a composite of the site, which is the spelling the composition law's transports use; written in
directly, the objects would be fixed at the composite-of-schemes spelling instead, and
reconciling the two under the associated-module functor and the identification of the sites costs
about thirty seconds each — see the implementation notes. -/
theorem pullbackComp_comp_eqToHom (hsq : j ≫ a = b ≫ j')
    (hA : (Scheme.Modules.pullback (B.inclusion.map (b ≫ j').left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) =
        (Scheme.Modules.pullback (B.inclusion.map (j ≫ a).left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
    (u : (Scheme.Modules.pullback (B.inclusion.map b.left)).obj
          ((Scheme.Modules.pullback (B.inclusion.map j'.left)).obj
            (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)) ⟶
        (Scheme.Modules.pullback (B.inclusion.map (b ≫ j').left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
    (hu : u = (Scheme.Modules.pullbackComp (B.inclusion.map b.left)
        (B.inclusion.map j'.left)).hom.app
      (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
    (v : (Scheme.Modules.pullback (B.inclusion.map j.left)).obj
          ((Scheme.Modules.pullback (B.inclusion.map a.left)).obj
            (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)) ⟶
        (Scheme.Modules.pullback (B.inclusion.map (j ≫ a).left)).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
    (hv : v = (Scheme.Modules.pullbackComp (B.inclusion.map j.left)
        (B.inclusion.map a.left)).hom.app
      (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)) :
    u ≫ eqToHom hA =
    (Stacks.ClosedImmersion.pullbackCompIso
        (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
        (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
        (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
        (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
        (toShHom_square_of_comp_eq B S hS j j' b a hsq)
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫ v := by
  subst hu
  subst hv
  refine ((Iso.eq_comp_inv (Iso.app (Scheme.Modules.pullbackComp
    (B.inclusion.map j.left) (B.inclusion.map a.left))
      (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))).mp ?_).symm
  rw [pullbackCompIso_hom_eq_pullbackComp B S hS j j' b a hsq,
    pullbackCompIso_eqToHom_app_eq B S hS j j' b a hsq hA, Category.assoc]
  rfl




/-- **The transport of the inverse-image functors along the commutativity of the square of
represented algebraic spaces, read at a module, is a transport of the two objects.**

The transport appearing in `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app` is the
`CategoryTheory.NatTrans.app` of an `eqToHom` of functors indexed by the morphisms of
`AlgebraicGeometry.AlgebraicSpaces`; the composition law
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp` is indexed by the morphisms
of the site, and its transport is a plain `eqToHom` of objects.  This identifies the two.

`rfl` for this is a **kernel deterministic timeout**, even at a variable module, because
`CategoryTheory.NatTrans.app` of a stuck `Eq.rec` is a projection the kernel cannot take.
Rewriting `CategoryTheory.eqToHom_app` first, so that one side is a plain `eqToHom`, makes it
free (0.2 s).  The target transport is a hypothesis so that no spelling of the composite of the
square's two routes other than `φ(b) ≫ φ(j')` occurs in the statement. -/
theorem eqToHom_app_representedSpaceMap_square (hsq : j ≫ a = b ≫ j')
    (M : Modules.{u, u} B S hS (yoneda.obj V') (isAlgebraicSpace_yoneda B S hS V'))
    (hΦ : (modulePullback B S hS (representedSpaceMap B S hS b ≫
            representedSpaceMap B S hS j')).obj M =
        (modulePullback B S hS (representedSpaceMap B S hS j ≫
            representedSpaceMap B S hS a)).obj M) :
    (eqToHom (congrArg
          (fun h : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ => modulePullback B S hS h)
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq).symm)).app M =
      eqToHom hΦ := by
  rw [eqToHom_app]


/-- **The transport at one of the two composites around the square carries the transport of its
source to the transport of its target.**  For two morphisms `m` and `m'` of the site and an
equality `m = m'`, the transport of the inverse image at `m'` followed by any transport of its
target is any transport of its source followed by the transport at `m`.

True by `subst` **at plain variables, before any composite of the square appears**, which is why
`m` and `m'` are variables of the site rather than the two routes around the square: the equality
of those two routes cannot be substituted.  Both transports are hypotheses, so that an
instantiation can supply them at either spelling of the composite, and they are absorbed by
`CategoryTheory.comp_eqToHom_of_refl` and `CategoryTheory.eqToHom_comp_of_refl` in term position:
`rw` and `simp` with `CategoryTheory.eqToHom_refl` both report that they cannot find the pattern
here, which is the failure those two lemmas exist for. -/
theorem representedAssociatedModulePullbackIso_eqToHom {m m' : R ⟶ V'} (h : m = m')
    (hΦ : (modulePullback B S hS (representedSpaceMap B S hS m')).obj
          ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
        (modulePullback B S hS (representedSpaceMap B S hS m)).obj
          ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))))
    (hΨ : (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
            ((Scheme.Modules.pullback (B.inclusion.map m'.left)).obj
              (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
        (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
            ((Scheme.Modules.pullback (B.inclusion.map m.left)).obj
              (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))) :
    (representedAssociatedModulePullbackIso B S hS m'
            (relativelyRepresentable_yoneda_map B S hS m')
            (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫ eqToHom hΨ =
      eqToHom hΦ ≫ (representedAssociatedModulePullbackIso B S hS m
        (relativelyRepresentable_yoneda_map B S hS m)
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom := by
  subst h
  exact (CategoryTheory.comp_eqToHom_of_refl hΨ _).trans
    (CategoryTheory.eqToHom_comp_of_refl hΦ _).symm


/-- **The transport of the inverse image carries the ringed-space square comparison to the
spaces-side one**, read at `Stacks.ClosedImmersion.idealSheaf` of `j'`.

This is the hypothesis `hΞ` of
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso`, and with it the
naturality of part (1) of [Stacks Project, Tag 04G2] in the closed immersion is unconditional;
see `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`
below.

The proof instantiates the generic engine of
`StacksFrontier/CategoryTheory/SquareTransportConormal.lean` at the two instances of the composition
law `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_eq` and the three
residual steps proved above.  Every step of that engine is at plain variables; what the shape of
the instantiation below is arranged for is the **kernel**, and the arrangement is exactly the
three devices the implementation notes of this file record: the middle transport is reached by
`Stacks.CategoryTheory.mid_eq_of_reading`, which removes it from every composite; the transport
`δ` of the inner objects is taken twice, with `rfl` between the two spellings; and the two
transports whose spelling the goal fixes — the one at `b` read at
`Stacks.ClosedImmersion.conormalSheaf` and the one at `j` read at the pulled-back ideal sheaf —
are **supplied** to `Stacks.CategoryTheory.comp₃_mid_eq_of` and
`Stacks.CategoryTheory.cancel_left_of_comp₃` rather than inherited from the composition laws. -/
theorem representedAssociatedModulePullbackIso_squarePullbackCompIso
    (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS b)).map
            (representedAssociatedModulePullbackIso B S hS j'
              (relativelyRepresentable_yoneda_map B S hS j')
              (Stacks.ClosedImmersion.idealSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).inv ≫
          (squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
              (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
              (representedSpaceMap B S hS a)
              (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.app
            ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
                (Stacks.ClosedImmersion.idealSheaf
                  ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
        (representedAssociatedModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b)
              (Stacks.ClosedImmersion.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
                (Stacks.ClosedImmersion.pullbackCompIso
                    (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                    (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                    (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                    (toShHom_square_of_comp_eq B S hS j j' b a hsq)
                    (Stacks.ClosedImmersion.idealSheaf
                      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom) ≫
            (representedAssociatedModulePullbackIso B S hS j
                (relativelyRepresentable_yoneda_map B S hS j)
                ((Scheme.Modules.pullback (B.inclusion.map a.left)).obj
                  (Stacks.ClosedImmersion.idealSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))).inv ≫
              (modulePullback B S hS (representedSpaceMap B S hS j)).map
                (representedAssociatedModulePullbackIso B S hS a
                  (relativelyRepresentable_yoneda_map B S hS a)
                  (Stacks.ClosedImmersion.idealSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).inv := by
  -- hA : the transport of the two pulled-back ideal sheaves, schemes side
  have hA : (Scheme.Modules.pullback (B.inclusion.map (b ≫ j').left)).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) =
      (Scheme.Modules.pullback (B.inclusion.map (j ≫ a).left)).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :=
    congrArg (fun m : R ⟶ V' => (Scheme.Modules.pullback (B.inclusion.map m.left)).obj
      (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)) hsq.symm
  -- hPsi : the same transport under the associated module and the identification of the sites
  have hΨ : (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          ((Scheme.Modules.pullback (B.inclusion.map (b ≫ j').left)).obj
            (Stacks.ClosedImmersion.idealSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
      (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          ((Scheme.Modules.pullback (B.inclusion.map (j ≫ a).left)).obj
            (Stacks.ClosedImmersion.idealSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) :=
    congrArg (fun m : R ⟶ V' => (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
        ((Scheme.Modules.pullback (B.inclusion.map m.left)).obj
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))) hsq.symm
  -- hPhi : the transport along the commutativity of the square of represented spaces,
  -- at the COMPOSITE-OF-REPRESENTED-MAPS spelling (the reading's)
  have hΦ : (modulePullback B S hS (representedSpaceMap B S hS b ≫
            representedSpaceMap B S hS j')).obj
          ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
              (Stacks.ClosedImmersion.idealSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) =
      (modulePullback B S hS (representedSpaceMap B S hS j ≫
            representedSpaceMap B S hS a)).obj
          ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
              (Stacks.ClosedImmersion.idealSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) :=
    congrArg (fun h : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ =>
        (modulePullback B S hS h).obj
          ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
              (Stacks.ClosedImmersion.idealSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))))
      (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq).symm
  -- hx : the cancellation of the left-hand transport under the inverse image along b
  have hx := Stacks.CategoryTheory.map_inv_comp_map_hom
    (modulePullback B S hS (representedSpaceMap B S hS b))
    (representedAssociatedModulePullbackIso B S hS j'
      (relativelyRepresentable_yoneda_map B S hS j')
      (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
  -- hy : the cancellation of the right-hand transport under the inverse image along j
  have hy := Stacks.CategoryTheory.map_inv_comp_map_hom
    (modulePullback B S hS (representedSpaceMap B S hS j))
    (representedAssociatedModulePullbackIso B S hS a
      (relativelyRepresentable_yoneda_map B S hS a)
      (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
  -- hc, hc' : the composition comparison of the route j then a, read at the module
  have hc := Iso.hom_inv_id_app (modulePullbackCompIso B S hS (representedSpaceMap B S hS j)
      (representedSpaceMap B S hS a))
    ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))
  have hc' := Iso.inv_hom_id_app (modulePullbackCompIso B S hS (representedSpaceMap B S hS j)
      (representedSpaceMap B S hS a))
    ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))
  -- ht : the transport at the composite j then a is invertible
  have ht := Iso.hom_inv_id (representedAssociatedModulePullbackIso B S hS (j ≫ a)
    (relativelyRepresentable_yoneda_map B S hS (j ≫ a))
    (Stacks.ClosedImmersion.idealSheaf
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))
  -- the reading of the spaces-side square comparison
  have hreading := squarePullbackCompIso_hom_app_eqToHom B S hS
    (representedSpaceMap B S hS j) (representedSpaceMap B S hS j')
    (representedSpaceMap B S hS b) (representedSpaceMap B S hS a)
    (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)
    ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))) hΦ
  -- the transport identity
  have hmid := representedAssociatedModulePullbackIso_eqToHom B S hS j' hsq hΦ hΨ
  -- the ringed-space square comparison solved for the transport, pushed through two functors
  have hπ := Stacks.CategoryTheory.map_map_comp_eqToHom
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj R) R.left.property)
    (representedSmallEtaleModuleEquivalence B S hS R).functor
    (pullbackComp_comp_eqToHom B S hS j j' b a hsq hA _ rfl _ rfl) hΨ
  -- the composition law on the route b then j'
  have hL1 := representedAssociatedModulePullbackIso_comp_of_eq B S hS b j'
    (relativelyRepresentable_yoneda_map B S hS b)
    (relativelyRepresentable_yoneda_map B S hS j')
    (relativelyRepresentable_yoneda_map B S hS (b ≫ j'))
    (Stacks.ClosedImmersion.idealSheaf
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) _ rfl
  -- the composition law on the route j then a
  have hL2 := representedAssociatedModulePullbackIso_comp_of_eq B S hS j a
    (relativelyRepresentable_yoneda_map B S hS j)
    (relativelyRepresentable_yoneda_map B S hS a)
    (relativelyRepresentable_yoneda_map B S hS (j ≫ a))
    (Stacks.ClosedImmersion.idealSheaf
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) _ rfl
  -- hcc, hcc' : the composition comparison of the route b then j', read at the module
  have hcc := Iso.hom_inv_id_app (modulePullbackCompIso B S hS (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS j'))
    ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))
  have hcc' := Iso.inv_hom_id_app (modulePullbackCompIso B S hS (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS j'))
    ((representedSmallEtaleModuleEquivalence B S hS V').functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V') V'.left.property).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)))
  have hs := Stacks.CategoryTheory.mid_eq_of_reading hcc' hc' hreading
  have hL1' := Stacks.CategoryTheory.comp₃_mid_eq_of hL1
    (representedAssociatedModulePullbackIso B S hS b
      (relativelyRepresentable_yoneda_map B S hS b)
      (Stacks.ClosedImmersion.conormalSheaf
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom rfl
  have haux := Stacks.CategoryTheory.square_transport_aux_of_mid hmid hs hc' hL1' hπ rfl hx hcc hc
  have hrot := Stacks.CategoryTheory.cancel_left_of_comp₃ hL2 hy
    (representedAssociatedModulePullbackIso B S hS j
      (relativelyRepresentable_yoneda_map B S hS j)
      ((Scheme.Modules.pullback (B.inclusion.map a.left)).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))).hom rfl
  have hk := Stacks.CategoryTheory.eq_comp_of_cancel_left hrot
    (Iso.inv_hom_id (representedAssociatedModulePullbackIso B S hS j
      (relativelyRepresentable_yoneda_map B S hS j)
      ((Scheme.Modules.pullback (B.inclusion.map a.left)).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom))))
  exact Stacks.CategoryTheory.eq_of_comp_cancel_right haux hk hc ht


/-- **The naturality of the comparison of part (1) of [Stacks Project, Tag 04G2] in the closed
immersion, with nothing assumed.**

`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso` with its
hypothesis `hΞ` discharged by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_squarePullbackCompIso`. -/
theorem conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq
    [hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]
    (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (representedConormalKernelIdealZPowIso B S hS j').hom ≫
        (squarePullbackCompIso B S hS (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
            (representedSpaceMap B S hS a)
            (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq)).hom.app
          (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j') 1).toSheafOfModules ≫
          (modulePullback B S hS (representedSpaceMap B S hS j)).map
            (kernelIdealSquareMap B S hS (representedSpaceMap B S hS j)
              (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
              (representedSpaceMap B S hS a)
              (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1) =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.ClosedImmersion.conormalSheafMap
                (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) ≫
          (representedConormalKernelIdealZPowIso B S hS j).hom :=
  conormalSheafMap_representedConormalKernelIdealZPowIso B S hS j j' b a hsq
    (representedAssociatedModulePullbackIso_squarePullbackCompIso B S hS j j' b a hsq)

end AlgebraicGeometry.Space

end
