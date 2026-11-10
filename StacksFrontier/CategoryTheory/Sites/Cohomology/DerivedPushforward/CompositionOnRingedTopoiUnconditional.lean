module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived direct images on ringed topoi, with nothing left over

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(ℰ), 𝒪_ℰ)` be morphisms of
ringed topoi.  Stacks 0D6E asserts

`Rg_* ∘ Rf_* = R(g ∘ f)_*`

as functors `D(𝒪_𝒞) ⟶ D(𝒪_ℰ)`.

`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi.derivedPushforwardComparison` is the
canonical comparison `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` coming from the universal property of the
former, and `isIso_derivedPushforwardComparison` proves it invertible under the hypothesis
`PushforwardComputesDerived`, which `isIso_derivedPushforwardComparison_iff` shows to be
*equivalent* to the conclusion.  **This file discharges that hypothesis**, so Stacks 0D6E holds
with no input beyond the two morphisms of ringed topoi.

## How the hypothesis is discharged

The source's own proof is uniqueness of adjoints: `Rf_* ⋙ Rg_*` is a right adjoint of
`Lg^* ⋙ Lf^*` because each factor is (Stacks 07A6), that composite is `L(g ∘ f)^*` (Stacks
0D6D), and `R(g ∘ f)_*` is a right adjoint of `L(g ∘ f)^*` as well.  Both inputs are available
here — `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction` and
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso` — so
`derivedPushforwardCompIsoOfAdjoints` below is that isomorphism.

Uniqueness of right adjoints produces *an* isomorphism, characterized by the units of the three
adjunctions; the comparison of Stacks 0D6E is characterized instead by the universal property of
`R(g ∘ f)_*`.  Identifying the two is the whole of the remaining work, and it is the abstract
transposition argument
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, already
in the tree for the ringed-space analogue Stacks 0D5T, whose five inputs are supplied here:

* the compatibility of each derived counit with the degreewise one is Stacks 0FPI,
  `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac`;
* the factorization of the derived pullback composition isomorphism through the degreewise one is
  Stacks 0D6D, `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app`;
* the transposition coherence of the three derived adjunctions is
  `derivedAdjunction_comp_homEquiv` below, a formal consequence of
  `CategoryTheory.Adjunction.rightAdjointUniq`;
* the agreement of the two composition isomorphisms on the *homotopy* categories is
  `mapHomotopyCategory_pullbackToposComp_hom_app_comp_counit` below, which is induced degreewise
  from the defining property of `CategoryTheory.Adjunction.leftAdjointCompIso` — the construction
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` is built by — so the mates lemma
  `CategoryTheory.conjugateEquiv_counit_symm` closes it.

## Main definitions

* `derivedPushforwardCompIsoOfAdjoints`: the composition isomorphism
  `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` obtained from uniqueness of right adjoints.  It carries no
  hypothesis beyond the two morphism-of-sites assumptions.

## Main results

* `derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints`: the two composition
  isomorphisms agree, i.e. the canonical comparison of Stacks 0D6E followed by
  `derivedPushforwardCompIsoOfAdjoints` is the comparison of `R(g ∘ f)_*`.
* `pushforwardComputesDerived_canonical`, `pushforwardComputesDerived`: the hypothesis of
  `isIso_derivedPushforwardComparison` holds, first for the canonical derived pushforwards at the
  standard model and then for every presentation and every choice of derived categories.
* `isIso_derivedPushforwardComparison_unconditional`: **Stacks 0D6E**, for arbitrary
  presentations of the three derived pushforwards, and
  `derivedPushforwardCompIsoUnconditional` the same as a natural isomorphism.

## Implementation notes

*The shape chosen for the statement.*  Stacks 0D6E writes an equality of composite functors.
Equality of functors is not available: `Rf_* ⋙ Rg_*` and `R(g ∘ f)_*` are total derived functors
of different functors on the homotopy category, equal only up to canonical isomorphism.  So the
tag goes on the invertibility of the *canonical* comparison, with the natural isomorphism
recorded alongside — exactly the two forms the pullback analogue Stacks 0D6D takes in
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi`
(`isIso_derivedPullbackCompComparison` and `derivedPullbackCompIso`), and exactly the two forms
the ringed-space analogue Stacks 0D5T takes.  An existence statement would be weaker and a bare
`Iso` would not say *which* isomorphism, which is the whole content: uniqueness of adjoints
supplies an isomorphism of the two functors with no work at all, and the theorem is that it is
the comparison the universal property induces.

*Crossing the choices of derived category.*  Everything mentioning
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward` runs at
`HasDerivedCategory.standard`, since that is what Stacks 0D6D and 0FPI fix in this tree, and the
attribute is file-local so it is repeated here.  The passage to an arbitrary
`HasDerivedCategory` instance and an arbitrary presentation goes through
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`, which mentions no derived category at
all.

*The morphism-of-sites hypotheses.*  `AlgebraicGeometry.RingedToposSiteHom` records only that the
underlying functor is continuous; exactness of the inverse image is not a field of it, and it is
what makes the morphism a morphism of ringed *topoi*.  Both `hmosf` and `hmosg` are therefore
carried, exactly as in the Stacks 06YY, 07A6, 0FPI and 0D6D statements of this chain, and
both are genuinely used: `hmosf` and `hmosg` feed the two derived adjunctions of Stacks 07A6 and
the composition isomorphism of Stacks 0D6D.  The hypothesis for the composite is not a third
assumption: it is `AlgebraicGeometry.RingedToposSiteHom.isMorphismOfSites_comp_u`, which is
Stacks 03CC.  The final statement `isIso_derivedPushforwardComparison_unconditional` is
unconditional in the sense that matters — the residual `PushforwardComputesDerived` of
`isIso_derivedPushforwardComparison` is gone — while still carrying `hmosf` and `hmosg`.

*Why the abstract transposition lemma is imported rather than restated.*
`compUnit_comp_compIso_of_adjunctions` is stated over arbitrary categories, functors and
adjunctions; it lives in the ringed-space file only because that is where it was first needed.
Importing it costs one cross-tree import and saves restating a forty-line chase.  Its abstract
form is also what makes it usable: run directly on the derived functors, which are reducible
abbreviations, a single `rw` of counit naturality exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 03CC](https://stacks.math.columbia.edu/tag/03CC)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

namespace Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi

universe u w dX dY dZ

section Degreewise

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two composition isomorphisms agree, on sheaves of modules.**  Reading the
direct-image composition isomorphism through `g^*` and the counit of `g`, then through `f^*` and
the counit of `f`, is the same as reading the inverse-image composition isomorphism through the
counit of `g ∘ f`.

This is the defining property of `CategoryTheory.Adjunction.leftAdjointCompIso`, which is how
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` is built from
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso`; the mates lemma
`CategoryTheory.conjugateEquiv_counit_symm` is that property. -/
theorem pullbackToposCompIso_hom_app_comp_counit
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    f.pullbackTopos.map (g.pullbackTopos.map
            ((RingedToposSiteHom.pushforwardToposCompIso f g).hom.app A) ≫
          g.pullbackPushforwardAdjunctionTopos.counit.app (f.pushforwardTopos.obj A)) ≫
        f.pullbackPushforwardAdjunctionTopos.counit.app A =
      (RingedToposSiteHom.pullbackToposCompIso f g).hom.app
          ((g.comp f).pushforwardTopos.obj A) ≫
        (g.comp f).pullbackPushforwardAdjunctionTopos.counit.app A := by
  have h := CategoryTheory.conjugateEquiv_counit_symm
    (g.comp f).pullbackPushforwardAdjunctionTopos
    (g.pullbackPushforwardAdjunctionTopos.comp f.pullbackPushforwardAdjunctionTopos)
    (RingedToposSiteHom.pushforwardToposCompIso f g).hom A
  dsimp at h
  rw [RingedToposSiteHom.pullbackToposCompIso, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]
  simpa [Adjunction.comp_counit_app] using h

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `pullbackToposCompIso_hom_app_comp_counit` on cochain complexes.  Every map in sight is
degreewise, so the identity holds degree by degree. -/
theorem mapHomologicalComplex_pullbackToposComp_hom_app_comp_counit
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((g.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso
                (RingedToposSiteHom.pushforwardToposCompIso f g).symm
                  (ComplexShape.up ℤ)).inv.app K) ≫
            (Adjunction.mapHomologicalComplexAdjunction
                g.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).counit.app
              ((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).counit.app K =
      (Functor.mapHomologicalComplexCompIso
            (RingedToposSiteHom.pullbackToposCompIso f g) (ComplexShape.up ℤ)).hom.app
          (((g.comp f).pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            (g.comp f).pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).counit.app K :=
  HomologicalComplex.hom_ext _ _ fun n =>
    pullbackToposCompIso_hom_app_comp_counit f g (K.X n)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `pullbackToposCompIso_hom_app_comp_counit` on the unbounded homotopy categories.  This is the
one input of `Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`
that is not formal. -/
theorem mapHomotopyCategory_pullbackToposComp_hom_app_comp_counit
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :
    (f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((g.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map
              ((Functor.mapHomotopyCategoryCompIso
                (RingedToposSiteHom.pushforwardToposCompIso f g).symm
                  (ComplexShape.up ℤ)).inv.app K) ≫
            (homotopyPullbackPushforwardAdjunction g).counit.app
              ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (homotopyPullbackPushforwardAdjunction f).counit.app K =
      (pullbackOnHomotopyCompIso f g).hom.app
          (((g.comp f).pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (homotopyPullbackPushforwardAdjunction (g.comp f)).counit.app K := by
  obtain ⟨K⟩ := K
  exact congrArg (HomotopyCategory.quotient _ _).map
    (mapHomologicalComplex_pullbackToposComp_hom_app_comp_counit f g K)

end Degreewise

section Resolution

variable {Y Z : RingedTopos.{w, w, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
  (g : RingedToposSiteHom Y Z)
  (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)

omit [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Invertibility of a comparison, read on complexes.**  For a right derived functor of
degreewise pushforward along `g`, the comparison is invertible at an object `M` of `K(𝒪_𝒟)`
exactly when degreewise `g_*` carries one K-injective resolution of `M` to a quasi-isomorphism.

The right-hand side mentions neither the presentation `(Rg, αg)` nor the chosen derived
categories, which is what lets a statement proved for one choice be transported to any other.
The proof is the naturality square of `αg` along the resolution: its other three edges are
invertible, the comparison at a K-injective complex by Stacks 070K and the image of the
resolution because localization inverts quasi-isomorphisms. -/
theorem isIso_app_iff_quasiIso_pushforwardOnHomotopy
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))]
    (M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))
    (J : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hJ : J.IsKInjective)
    (s : M ⟶ (HomotopyCategory.quotient
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) s) :
    IsIso (αg.app M) ↔
      HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
          (ComplexShape.up ℤ)
        ((g.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  have hnat := αg.naturality s
  dsimp only [Functor.comp_map] at hnat
  have := isIso_app_of_isKInjective.{w, dY, dZ} g Rg αg J hJ
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)) s hs
  rw [← DerivedCategory.isIso_Qh_map_iff]
  exact ⟨fun _ => IsIso.of_isIso_fac_right hnat, fun _ => IsIso.of_isIso_fac_right hnat.symm⟩

end Resolution

noncomputable section Canonical

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)

/-! The three instance arguments of `Lf^*`, `Lg^*` and `L(g ∘ f)^*` are not residual
hypotheses: they are `Prop` classes, discharged for every morphism of ringed topoi by Stacks
06YY, and by proof irrelevance the derived pullbacks do not depend on the witness.  They are
carried through this section only because those functors cannot be written down without them,
and are discharged by `hasLeftDerivedFunctor_pullbackOnHomotopy` in
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` below. -/

section WithDerivedPullback

variable
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ))]

/-- The composite of the two derived adjunctions of Stacks 07A6, transported along the derived
pullback composition isomorphism of Stacks 0D6D: an adjunction `L(g ∘ f)^* ⊣ Rf_* ⋙ Rg_*`. -/
def derivedCompAdjunction :
    derivedPullback (g.comp f) ⊣ derivedPushforward f ⋙ derivedPushforward g :=
  ((derivedAdjunction g hmosg).comp
      (derivedAdjunction f hmosf)).ofNatIsoLeft
    (derivedPullbackCompIso f g hmosf hmosg)

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` for the canonical derived
pushforwards.

Both functors are right adjoints of `L(g ∘ f)^*`: the composite of the two derived adjunctions of
Stacks 07A6 is an adjunction `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`, and Stacks 0D6D identifies its left
side with `L(g ∘ f)^*`.  The isomorphism is the uniqueness isomorphism of right adjoints, which
is the construction the source's proof of Stacks 0D6E uses. -/
def derivedPushforwardCompIsoOfAdjoints :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (g.comp f) :=
  Adjunction.rightAdjointUniq (derivedCompAdjunction f g hmosf hmosg)
    (derivedAdjunction (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))

/-- The derived adjunction for a composite is the composite adjunction, transported along the
composition isomorphisms for derived pullback and derived pushforward.

Two adjunctions between the same pair of functors agree as soon as their units do, and the unit
of the uniqueness isomorphism of right adjoints is defined so that they do. -/
theorem derivedCompAdjunction_ofNatIsoRight :
    (derivedCompAdjunction f g hmosf hmosg).ofNatIsoRight
        (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg) =
      derivedAdjunction (g.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) :=
  Adjunction.ext (Adjunction.unit_rightAdjointUniq_hom _ _)

/-- Transposition under the derived adjunction for a composite agrees with successive
transposition under the two derived adjunctions and the canonical composition maps.  This is the
composition coherence needed for vertical pasting of mates, and the one input of
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions` that is
about `derivedPushforwardCompIsoOfAdjoints` itself. -/
theorem derivedAdjunction_comp_homEquiv
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : (derivedPullback (g.comp f)).obj M ⟶ K) :
    (derivedAdjunction g hmosg).homEquiv _ _
          ((derivedAdjunction f hmosf).homEquiv _ _
            ((derivedPullbackCompIso f g hmosf
              hmosg).hom.app M ≫ φ)) ≫
        (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg).hom.app K =
      (derivedAdjunction (g.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).homEquiv M K φ := by
  have h := congrArg (fun a => a.homEquiv M K φ)
    (derivedCompAdjunction_ofNatIsoRight f g hmosf hmosg)
  simpa only [derivedCompAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv, Equiv.trans_apply] using h

/-- **The two composition isomorphisms for derived pushforward agree.**  The comparison from
degreewise pushforward along `g ∘ f` to `Rf_* ⋙ Rg_*` of Stacks 0D6E, followed by the uniqueness
isomorphism `derivedPushforwardCompIsoOfAdjoints`, is the canonical comparison of `R(g ∘ f)_*`.

Both maps `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` are therefore the same, and so the first is invertible.
The chase is the abstract
`Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, whose
inputs are Stacks 0FPI for each of the three morphisms, Stacks 0D6D in its characterized form,
the transposition coherence above, and the degreewise agreement of the two composition
isomorphisms. -/
theorem derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :
    (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
            (derivedPushforwardUnit f) (derivedPushforwardUnit g)).app K ≫
        (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg).hom.app
          (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit (g.comp f)).app K := by
  rw [derivedPushforwardCompUnit_app.{u, u + 1, u + 1, u + 1} f g (derivedPushforward f)
    (derivedPushforward g) (derivedPushforwardUnit f) (derivedPushforwardUnit g) K]
  exact DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions
    (homotopyPullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction g)
    (homotopyPullbackPushforwardAdjunction (g.comp f))
    (derivedAdjunction f hmosf)
    (derivedAdjunction g hmosg)
    (derivedAdjunction (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    (Functor.mapHomotopyCategoryCompIso
      (RingedToposSiteHom.pushforwardToposCompIso f g).symm (ComplexShape.up ℤ))
    (pullbackOnHomotopyCompIso f g)
    (derivedPullbackCompIso f g hmosf hmosg)
    (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg)
    (derivedAdjunction_counit_fac f hmosf)
    (derivedAdjunction_counit_fac g hmosg)
    (derivedAdjunction_counit_fac (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g)
    (derivedAdjunction_comp_homEquiv f g hmosf hmosg)
    (mapHomotopyCategory_pullbackToposComp_hom_app_comp_counit f g) K

include hmosf hmosg in
/-- The composite `Rf_* ⋙ Rg_*`, with the comparison `derivedPushforwardCompUnit`, is a right
derived functor of degreewise pushforward along `g ∘ f`: it is `R(g ∘ f)_*` read through
`derivedPushforwardCompIsoOfAdjoints`. -/
theorem isRightDerivedFunctor_comp_canonical :
    (derivedPushforward f ⋙ derivedPushforward g).IsRightDerivedFunctor
      (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
        (derivedPushforwardUnit f) (derivedPushforwardUnit g))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)) := by
  refine (Functor.isRightDerivedFunctor_iff_of_iso (derivedPushforwardUnit (g.comp f)) _ _
    (derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg).symm ?_).1 inferInstance
  refine NatTrans.ext (funext fun K => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
  rw [← derivedPushforwardCompUnit_comp_derivedPushforwardCompIsoOfAdjoints f g hmosf hmosg K,
    Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

include hmosf hmosg in
/-- **`PushforwardComputesDerived` holds for the canonical derived pushforward along `g`.**  This
is the hypothesis that the whole of Stacks 0D6E was reduced to, now discharged at the standard
model. -/
theorem pushforwardComputesDerived_canonical :
    PushforwardComputesDerived.{u, u + 1, u + 1} f g (derivedPushforward g)
      (derivedPushforwardUnit g) :=
  (isIso_derivedPushforwardComparison_iff.{u, u + 1, u + 1, u + 1} f g (derivedPushforward f)
      (derivedPushforward g) (derivedPushforward (g.comp f)) (derivedPushforwardUnit f)
      (derivedPushforwardUnit g) (derivedPushforwardUnit (g.comp f))).1
    ((Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedPushforward (g.comp f))
        (derivedPushforwardUnit (g.comp f))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ))
        (derivedPushforward f ⋙ derivedPushforward g)
        (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
          (derivedPushforwardUnit f) (derivedPushforwardUnit g))).1
      (isRightDerivedFunctor_comp_canonical f g hmosf hmosg))

end WithDerivedPullback

include hmosf hmosg in
/-- **The composition formula, with no derived category in the statement.**  If `I` is a
K-injective complex of `𝒪_𝒞`-modules and `s` is a quasi-isomorphism from `f_* I` to a K-injective
complex of `𝒪_𝒟`-modules, then `g_* s` is a quasi-isomorphism.

This is `pushforwardComputesDerived_canonical` read through
`isIso_app_iff_quasiIso_pushforwardOnHomotopy`.  Because it mentions no derived category, it is
the form in which the result holds for *every* choice of derived categories, which is what
`pushforwardComputesDerived` then uses. -/
theorem quasiIso_mapHomotopyCategory_pushforward_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective)
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hJ : J.IsKInjective)
    (s : (f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj I) ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ)
      ((g.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmosf
  have := hasLeftDerivedFunctor_pullbackOnHomotopy g hmosg
  have := hasLeftDerivedFunctor_pullbackOnHomotopy (g.comp f)
    (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)
  rw [← isIso_app_iff_quasiIso_pushforwardOnHomotopy.{u, u + 1, u + 1} g (derivedPushforward g)
    (derivedPushforwardUnit g) _ J hJ s hs]
  exact pushforwardComputesDerived_canonical f g hmosf hmosg I hI

end Canonical

section General

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dZ} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)
  (Rf : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (Rg : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
  (Rh : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
  (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
  (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
  (αh : pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ Rh)

omit [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
include hmosf hmosg in
/-- **The hypothesis of Stacks 0D6E holds unconditionally.**  Degreewise pushforward along `f`
carries every K-injective complex of `𝒪_𝒞`-modules to a complex computing any derived pushforward
along `g`, for every choice of derived categories and every presentation of that derived
pushforward.

A K-injective resolution of `f_* I` exists, and
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` says that `g_*` carries it to a
quasi-isomorphism; `isIso_app_iff_quasiIso_pushforwardOnHomotopy` turns that back into
invertibility of the comparison. -/
theorem pushforwardComputesDerived
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))] :
    PushforwardComputesDerived f g Rg αg := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ := exists_quasiIso_isKInjective Y
    ((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hmem : HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).map s) := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (isIso_app_iff_quasiIso_pushforwardOnHomotopy.{w, dY, dZ} g Rg αg _ J hJ _ hmem).2
    (quasiIso_mapHomotopyCategory_pushforward_of_isKInjective f g hmosf hmosg I hI J hJ _ hmem)

include hmosf hmosg in
/-- **Stacks 0D6E.**  For composable morphisms of ringed topoi `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)`
and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(ℰ), 𝒪_ℰ)`, the canonical comparison from a derived pushforward along
`g ∘ f` to the composite of derived pushforwards along `f` and `g` is an isomorphism, so
`Rg_* ∘ Rf_* = R(g ∘ f)_*` as functors `D(𝒪_𝒞) ⟶ D(𝒪_ℰ)`.

No hypothesis beyond the two morphisms and the three presentations of the derived pushforwards:
the condition `PushforwardComputesDerived`, which `isIso_derivedPushforwardComparison_iff` shows
to be equivalent to this statement, is discharged by `pushforwardComputesDerived`. -/
@[stacks 0D6E]
theorem isIso_derivedPushforwardComparison_unconditional
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) :=
  isIso_derivedPushforwardComparison f g Rf Rg Rh αf αg αh
    (pushforwardComputesDerived f g hmosf hmosg Rg αg)

include hmosf hmosg in
/-- **Stacks 0D6E as a natural isomorphism** `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*`, obtained by inverting
the canonical comparison.  This is the source's equality of composite functors, in the only form
in which it can hold: the two functors are total derived functors of different functors on the
homotopy category, so they agree up to the canonical isomorphism and not on the nose. -/
@[stacks 0D6E "as a natural isomorphism"]
noncomputable def derivedPushforwardCompIsoUnconditional
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))] :
    Rf ⋙ Rg ≅ Rh :=
  derivedPushforwardCompIso f g Rf Rg Rh αf αg αh
    (pushforwardComputesDerived f g hmosf hmosg Rg αg)

/-- The underlying map of `derivedPushforwardCompIsoUnconditional` is the inverse of the
canonical comparison of Stacks 0D6E, so the characterization of that comparison applies to it. -/
theorem derivedPushforwardCompIsoUnconditional_inv
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ))] :
    (derivedPushforwardCompIsoUnconditional f g hmosf hmosg Rf Rg Rh αf αg αh).inv =
      derivedPushforwardComparison f g Rf Rg Rh αf αg αh :=
  rfl

end General

end Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi

end
