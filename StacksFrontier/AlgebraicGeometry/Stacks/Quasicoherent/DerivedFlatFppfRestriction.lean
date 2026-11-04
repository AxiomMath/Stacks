module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticPullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The kernel of derived restriction to the flat-fppf site

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the morphism of
ringed topoi of **Stacks 0788** (2).  Pullback of sheaves of modules along `g` is restriction to
the flat objects (**Stacks 0788**, `flat_ringed`) and is exact, so it needs no derivation: it acts
on the unbounded derived categories degreewise.

**Stacks 07B9** (2)(b) says that for a complex `K` of `𝒪_𝒳`-modules lying in
`D_{LQCoh^fbc}(𝒪_𝒳)`, the pullback `g^*K` vanishes exactly when `K` lies in
`D_{𝒫_𝒳}(𝒪_𝒳)`, where `𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.  That is what is proved here.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.flatFppfModules`: the category `Mod(𝒪_{𝒳_{flat,fppf}})` of
  sheaves of modules on the flat-fppf site, over the restricted structure sheaf.
* `AlgebraicGeometry.Stack.FlatFppf.derivedModuleRestriction`: the functor
  `g^* : D(𝒪_𝒳) ⥤ D(𝒪_{𝒳_{flat,fppf}})`, restriction applied degreewise.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction_exact`: restriction of sheaves of modules to
  the flat-fppf site is exact.
* `AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`: **Stacks 07AR** (2)
  read at `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction` rather than at the pullback of
  **Stacks 03D6**, the two being identified by **Stacks 0788**, `flat_ringed`.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic`: the
  kernel of `g^*` on the unbounded derived category, with no hypothesis on `K` at all: `g^*K = 0`
  exactly when every cohomology module of `K` is parasitic.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff`: **Stacks 07B9** (2)(b)
  in the form the source states it, over `D_{LQCoh^fbc}(𝒪_𝒳)` and with
  `𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` on the right-hand side.

## Implementation notes

### What is proved and what is taken from elsewhere

The parasitic condition on a *single* module is identified with vanishing of its restriction by
**Stacks 07AR** (2),
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_pullbackModules`.  Everything added here
is the passage to complexes, and it is unconditional: an object of a derived category vanishes
exactly when all of its cohomology objects do
(`DerivedCategory.isZero_iff_forall_isZero_homology`), and `g^*` being exact its cohomology
objects are the restrictions of those of `K`
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`).  So the two conditions match degree by
degree.

The source states (2)(b) with `ℱ^•` ranging over `D_{LQCoh^fbc}(𝒪_𝒳)` and concludes membership in
`D_{𝒫_𝒳}(𝒪_𝒳)` for the *intersection* `𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.  Both halves are
kept: `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff` takes the membership
of `K` in `D_{LQCoh^fbc}(𝒪_𝒳)` as a hypothesis and concludes membership in the derived category of
the intersection, which is
`AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChange`,
the very subcategory the Verdier quotient of **Stacks 07B6** divides by.  The local
quasi-coherence and flat base change half of the conclusion is free given the hypothesis, which
is the content of
`AlgebraicGeometry.Stack.inverseImage_derivedParasiticLocallyQuasicoherentFlatBaseChange`;
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic` records
the hypothesis-free statement underneath it.

### Exactness of restriction, and why it is taken at the ringed topos

Restriction of sheaves of modules to the flat-fppf site is exact because the flat-fppf morphism of
ringed topoi is *flat* — its inverse-image structure map is an isomorphism, **Stacks 0788**,
`flat_ringed`, proved as `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism_isFlat` — and
pullback of modules along a flat morphism of ringed topoi is exact
(`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`).  Exactness is then
transported to `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction` along **Stacks 0788**,
`flat_ringed`.

The route through the underlying abelian sheaves — restriction of modules composed with
`SheafOfModules.toSheaf` is `SheafOfModules.toSheaf` composed with restriction of abelian sheaves,
and the latter is exact by continuity and cocontinuity of the inclusion — is *not* available at
this module universe: it needs `SheafOfModules.toSheaf` to preserve finite colimits, which asks
the module universe to contain the universe `u + 1` of the objects of the site, whereas the
structure sheaf of **Stacks 06TV** has its sections in `Type u` and the derived category of
**Stacks 07B6** is formed at that universe.  The ringed-topos route has no such restriction.

### The universes, and the two instance hypotheses

The module universe is `u`, the universe of the sections of the structure sheaf of
**Stacks 06TV**, which is where `AlgebraicGeometry.Stack.fppfModules` and hence the whole of
**Stacks 07B6** lives.  At that universe both module categories are abelian: the two sites have
their objects in `Type (u + 1)` and their morphisms in `Type u`, hence are essentially small in
`Type (u + 1)`, and essential smallness gives sheafification of `AddCommGrpCat.{u}`-valued
presheaves and identifies the sheafification equivalences with the local bijections.  Those are
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_associatedTopology_ab` and
`AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat` for the fppf
site — restated below at the other spelling of its topology, see the section note — and the
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_addCommGrpCat` for the flat-fppf one.
So nothing below carries the abelian structure as a hypothesis, unlike
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherent.lean`, which does; the
statements there specialize to these instances.

What *is* carried is the choice of a localization universe for each of the two derived categories,
`HasDerivedCategory.{t}` and `HasDerivedCategory.{t'}`, exactly as in that file.  Both are
discharged by `CategoryTheory.HasDerivedCategory.standard`, so nothing here is vacuous.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w t t'

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-! ### The fppf site at the `AlgebraicGeometry.SiteKind` spelling of its topology

The fppf topology of an algebraic stack has two spellings in the library:
`AlgebraicGeometry.Stack.FlatFppf.fppfTopology`, which is
`AlgebraicGeometry.Stack.associatedTopology` at `B.topology`, and
`AlgebraicGeometry.BigFppfOver.associatedTopology` at `AlgebraicGeometry.SiteKind.fppf`, which is
the one the structure sheaf of **Stacks 06TV** that `AlgebraicGeometry.Stack.fppfModules` is
formed over lives on.  They are definitionally equal but not syntactically so, and instance
search keys on the syntax, so both spellings have to be available as instances.

At the first spelling they are
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_associatedTopology_ab` and
`AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat`.  The two
statements below are those same two statements at the second spelling: their proofs are the
existing ones, so nothing is re-derived. -/

/-- `AlgebraicGeometry.Stack.FlatFppf.hasSheafify_associatedTopology_ab` at the
`AlgebraicGeometry.SiteKind.fppf` spelling of the fppf topology of an algebraic stack. -/
theorem hasSheafify_fppf_addCommGrpCat :
    HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{u} :=
  hasSheafify_associatedTopology_ab.{u, w, u} B S hS 𝒳

/-- `AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat` at the
`AlgebraicGeometry.SiteKind.fppf` spelling of the fppf topology of an algebraic stack. -/
theorem wEqualsLocallyBijective_fppf_addCommGrpCat :
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat B S hS 𝒳

attribute [local instance] hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-- The category `Mod(𝒪_{𝒳_{flat,fppf}})` of sheaves of modules on the flat-fppf site of an
algebraic stack, over the restricted structure sheaf of **Stacks 0788**, `flat_ringed`.  This is
the target of restriction from `Mod(𝒪_𝒳)`. -/
abbrev flatFppfModules :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ringedTopos B S hS 𝒳).O)

/-- **Restriction of sheaves of modules to the flat-fppf site is exact.**

The flat-fppf morphism of ringed topoi is flat (**Stacks 0788**, `flat_ringed`), and pullback of
sheaves of modules along a flat morphism of ringed topoi is exact; **Stacks 0788**,
`flat_ringed` identifies that pullback with restriction. -/
theorem moduleRestriction_exact :
    exactFunctor (fppfModules B S hS 𝒳) (flatFppfModules B S hS 𝒳)
      (moduleRestriction B S hS 𝒳) :=
  (exactFunctor _ _).prop_of_iso (modulePullbackIso B S hS 𝒳)
    (pullbackModules_exact_of_isFlatMap
      (ringedToposMorphism B S hS 𝒳) (ringedToposMorphism_isFlat B S hS 𝒳))

/-- Restriction of sheaves of modules to the flat-fppf site is additive, being exact. -/
instance moduleRestriction_additive : (moduleRestriction B S hS 𝒳).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (moduleRestriction_exact B S hS 𝒳)

/-- Restriction of sheaves of modules to the flat-fppf site preserves finite limits. -/
instance moduleRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestriction B S hS 𝒳) :=
  ((exactFunctor_iff _).mp (moduleRestriction_exact B S hS 𝒳)).1

/-- Restriction of sheaves of modules to the flat-fppf site preserves finite colimits. -/
instance moduleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestriction B S hS 𝒳) :=
  ((exactFunctor_iff _).mp (moduleRestriction_exact B S hS 𝒳)).2

section Derived

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]

/-- `AlgebraicGeometry.Stack.fppfModules`, the category `Mod(𝒪_𝒳)` of **Stacks 07B6**, and the
category of modules over the structure sheaf of the fppf ringed topos of **Stacks 0788**, which is
the source of `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction`, are the same category: the two
sheaves of rings are the same sheaf of rings.  This records the choice of localization universe
for the one as a choice for the other, so that a single hypothesis serves both spellings. -/
instance hasDerivedCategory_ambientModules :
    HasDerivedCategory.{t} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O)) :=
  inferInstanceAs (HasDerivedCategory.{t} (fppfModules B S hS 𝒳))

/-- **The functor `g^* : D(𝒪_𝒳) ⥤ D(𝒪_{𝒳_{flat,fppf}})`.**  Restriction of sheaves of modules to
the flat-fppf site is exact, so no derivation is needed: it acts on the unbounded derived
categories degreewise. -/
abbrev derivedModuleRestriction :
    DerivedCategory (fppfModules B S hS 𝒳) ⥤ DerivedCategory (flatFppfModules B S hS 𝒳) :=
  (moduleRestriction B S hS 𝒳).mapDerivedCategory

end Derived

/-- **Stacks 07AR** (2), read at restriction rather than at the pullback of **Stacks 03D6**.  A
sheaf of `𝒪_𝒳`-modules is parasitic exactly when its restriction to the flat-fppf site vanishes.

This is `AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_pullbackModules` transported
along the identification of pullback with restriction of **Stacks 0788**, `flat_ringed`. -/
theorem isParasitic_iff_isZero_moduleRestriction (F : fppfModules B S hS 𝒳) :
    IsParasitic B S hS 𝒳 .fppf F.val ↔ IsZero ((moduleRestriction B S hS 𝒳).obj F) :=
  (isParasitic_iff_isZero_pullbackModules B S hS 𝒳 F).trans
    ((modulePullbackIso B S hS 𝒳).app F).isZero_iff

/-- **Restriction to the flat-fppf site is the identity on sections over a flat object.**  This
pins `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction` down: it is restriction along the
inclusion of the flat objects on the nose, with the same modules of sections, and in particular it
does not send every sheaf of modules to zero.  Both sides are literally the same proposition. -/
theorem subsingleton_moduleRestriction_obj_iff (F : fppfModules B S hS 𝒳)
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    Subsingleton (((moduleRestriction B S hS 𝒳).obj F).val.obj (op x)) ↔
      Subsingleton (F.val.obj (op ((objectProperty B S hS 𝒳).ι.obj x))) :=
  Iff.rfl

section Kernel

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]

/-- **The kernel of `g^*` on the unbounded derived category, with no hypothesis on `K`.**  For a
complex `K` of `𝒪_𝒳`-modules, the restriction `g^*K` to the flat-fppf site vanishes exactly when
every cohomology module of `K` is parasitic (**Stacks 0773**).

Both sides are tested degree by degree: an object of a derived category vanishes exactly when all
its cohomology objects do, restriction is exact so the cohomology modules of `g^*K` are the
restrictions of those of `K`, and vanishing of the restriction of a module is the parasitic
condition by **Stacks 07AR** (2). -/
theorem isZero_derivedModuleRestriction_iff_forall_isParasitic
    (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    IsZero ((derivedModuleRestriction B S hS 𝒳).obj K) ↔
      ∀ n : ℤ, IsParasitic B S hS 𝒳 .fppf
        (((DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) n).obj K)).val := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  rw [isParasitic_iff_isZero_moduleRestriction]
  exact (((moduleRestriction B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).isZero_iff

/-- **Stacks 07B9** (2)(b).  Let `𝒳` be an algebraic stack and set
`𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.  For a complex `K` of `𝒪_𝒳`-modules lying in
`D_{LQCoh^fbc}(𝒪_𝒳)`, the restriction `g^*K` to the flat-fppf site of **Stacks 0787** vanishes
exactly when `K` lies in `D_{𝒫_𝒳}(𝒪_𝒳)`.

Here `g^*` is restriction along the inclusion of the flat objects, which is pullback along the
morphism of ringed topoi of **Stacks 0788** (2) by **Stacks 0788**, `flat_ringed`, and which needs
no derivation because it is exact.  `D_{𝒫_𝒳}(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChange`, the subcategory the
Verdier quotient of **Stacks 07B6** divides by.

The local quasi-coherence and flat base change half of the right-hand side is free given the
hypothesis on `K`; the content is the parasitic half, which is
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic`. -/
@[stacks 07B9 "part (2)(b), the kernel of g^* on D_LQCoh^fbc(𝒪_𝒳): g^*K = 0 exactly when K lies \
in D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳), with g^* restriction to the flat-fppf site"]
theorem isZero_derivedModuleRestriction_iff {E : BigEtaleSite.{u}} {h : E.cutoff = B.cutoff}
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K) :
    IsZero ((derivedModuleRestriction B S hS 𝒳).obj K) ↔
      derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 K := by
  rw [isZero_derivedModuleRestriction_iff_forall_isParasitic]
  exact ⟨fun hp n => ⟨hp n, hK n⟩, fun hp n => (hp n).1⟩

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **Stacks 07B9** (2)(d), the first step of its proof: `g^*` inverts the class of morphisms that
the Verdier quotient of **Stacks 07B6** inverts.

A morphism `f` of `D_{LQCoh^fbc}(𝒪_𝒳)` is inverted by that quotient exactly when its cone lies in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.  Restriction to the flat-fppf site is exact, hence triangulated,
so it carries a distinguished triangle on `f` to a distinguished triangle on `g^*f`; by
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic` the third
vertex of the image triangle vanishes, and a distinguished triangle with vanishing third vertex has
an invertible first map. -/
theorem isInvertedBy_derivedQuasicoherentW :
    (derivedQuasicoherentW B E h S hS 𝒳).IsInvertedBy
      ((derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι ⋙
        derivedModuleRestriction B S hS 𝒳) := by
  intro X Y f hf
  obtain ⟨Z, g, k, hT, hZ⟩ := hf
  have hZ0 : IsZero ((derivedModuleRestriction B S hS 𝒳).obj Z) :=
    (isZero_derivedModuleRestriction_iff_forall_isParasitic B S hS 𝒳 Z).2 fun n => (hZ n).1
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (Functor.map_distinguished (moduleRestriction B S hS 𝒳).mapDerivedCategory _ hT)).1 hZ0

/-- **Stacks 07B9** (2)(d), the functor `c`.  Restriction to the flat-fppf site descends along the
Verdier quotient of **Stacks 07B6** to a functor

`c : D_QCoh(𝒪_𝒳) ⥤ D(𝒪_{𝒳_{flat,fppf}})`,

by `AlgebraicGeometry.Stack.FlatFppf.isInvertedBy_derivedQuasicoherentW` and the universal property
of the quotient. -/
def derivedQuasicoherentModuleRestriction :
    derivedCategoryQuasicoherent B E h S hS 𝒳 ⥤ DerivedCategory (flatFppfModules B S hS 𝒳) :=
  Localization.lift _ (isInvertedBy_derivedQuasicoherentW B S hS 𝒳 E h)
    (toDerivedCategoryQuasicoherent B E h S hS 𝒳)

/-- **Stacks 07B9** (2)(d), the commutativity the functor `c` is characterized by: composing the
quotient functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` of **Stacks 07B6** with `c` gives back
restriction to the flat-fppf site.  This is what pins `c` down; it is the "inner triangle
commutes" of the source's proof. -/
@[stacks 07B9 "part (2)(d), the functor c : D_QCoh(𝒪_𝒳) ⥤ D(𝒪_{𝒳_flat,fppf}) that g^* induces on \
the Verdier quotient of 07B6, together with its factorization through the quotient functor; the \
mutual inverseness of c with Lg_! is not covered"]
def toDerivedCategoryQuasicoherentCompRestriction :
    toDerivedCategoryQuasicoherent B E h S hS 𝒳 ⋙
        derivedQuasicoherentModuleRestriction B S hS 𝒳 E h ≅
      (derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳).ι ⋙
        derivedModuleRestriction B S hS 𝒳 :=
  Localization.fac _ (isInvertedBy_derivedQuasicoherentW B S hS 𝒳 E h)
    (toDerivedCategoryQuasicoherent B E h S hS 𝒳)

end Kernel

end AlgebraicGeometry.Stack.FlatFppf

end
