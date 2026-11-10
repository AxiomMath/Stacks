module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections

/-!
# Derived global sections of modules along the augmentation of a hypercovering

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it, let `K` be a hypercovering of `C` and let `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the
ringed augmentation of Stacks 0D9W, with `O = a⁻¹O_C`. Stacks 0DA1 asserts that

`RΓ(C, E) = RΓ((C/K)_total, La^*E)`

for every object `E` of the *unbounded* derived category `D(O_C)`. The source deduces it from
Stacks 0DA0, that `E ⟶ R a_* La^* E` is an isomorphism, together with the factorisation
`RΓ((C/K)_total, -) = RΓ(C, -) ∘ R a_*` of Cohomology on Sites, Remark 21.14.4 — Stacks 08J6, or
alternatively Stacks 0D6H.

Both steps are carried out here, for sheaves of modules. Global sections of a sheaf of modules
are taken with the module structure forgotten, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/ForgettingTheModuleStructure.lean`:
the underlying abelian sheaf followed by Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of
the constant-sheaf functor, so that no terminal object of the site is needed. `RΓ` is the total
right derived functor of that on the unbounded derived category.

## Main definitions

* `AlgebraicGeometry.RingedTopos.moduleGlobalSections` and
  `.derivedModuleGlobalSections`: `Γ(C, -)` and `RΓ(C, -)` for sheaves of modules on a ringed
  topos, valued in abelian groups resp. in `D(Ab)`.
* `AlgebraicGeometry.RingedToposHom.derivedGlobalSectionsPushforwardIso`: **the derived half
  of Stacks 08J6 for a morphism of ringed topoi**, the factorisation
  `R f_* ⋙ RΓ(D, -) ≅ RΓ(C, -)`.
* `AlgebraicGeometry.RingedToposHom.derivedGlobalSectionsPullbackIso`: the isomorphism
  `RΓ(D, -) ≅ Lf^* ⋙ RΓ(C, -)` for a morphism of ringed topoi with invertible structure map.
* `Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsPullbackIsoOfHypercovering`:
  the same for the ringed augmentation of a hypercovering, which is **Stacks 0DA1**.

## Main results

* `AlgebraicGeometry.RingedToposHom.isKInjective_pushforwardModules`: **Stacks 093Y for a
  morphism of ringed topoi with invertible structure map** — degreewise `f_*` carries K-injective
  complexes of sheaves of modules to K-injective complexes. This is the one input of the derived
  factorisation that is not formal, and it is proved rather than assumed: `f_*` is the right
  adjoint of the exact functor `f^*`.

## What Stacks 0DA1 still lacks here

`Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsPullbackIsoOfHypercovering` carries
three named hypotheses, and says so in its clause string.

* `hunit` and `hacyclic` are the two inputs of this library's Stacks 0DA0, inherited unchanged
  from `Stacks.CategoryTheory.Hypercovering`
  `.isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`: the first is Stacks 0D8E in its
  module form, that the underived unit `M ⟶ a_*a^*M` is an
  isomorphism, and the second is that `a^*` of a K-injective complex computes `R a_*`. See the
  module docstring of `HypercoveringModuleCohomologicalDescent.lean`, in this directory, for why
  neither is available.
* `hΓ` is the **underived** identity `Γ(C, a_*M) = Γ((C/K)_total, M)` on sheaves of modules, on
  which Stacks 08J6 rests. It is the statement that the composition of `a` with the morphism to
  the punctual topos is the morphism to the punctual topos, and it is not available in this
  library for the same reason as its abelian counterpart, the hypothesis `hΓ` of this library's
  Stacks 0D8H: `CategoryTheory.Sheaf.Γ` is the right adjoint of
  `CategoryTheory.constantSheaf`, so the identity amounts to `a⁻¹` carrying a constant abelian
  sheaf to a constant abelian sheaf, and nothing in Mathlib or in this development says that.

What is *not* assumed is the derived content: the factorisation
`R a_* ⋙ RΓ(C, -) ≅ RΓ((C/K)_total, -)` is proved from `hΓ` by
`Stacks.Cohomology.LerayUnbounded.derivedCompIso`, whose hypothesis — that degreewise `a_*`
preserves K-injectivity — is discharged here.

## Implementation notes

**The unbounded case is reached, and no boundedness enters anywhere.** The conclusion is an
isomorphism of functors on the whole of `D(O_C)`, which is the form the source states. The two
ingredients are both unbounded: this library's Stacks 0DA0 is stated on all of `D(O_C)`, and
`derivedCompIso` compares total right derived functors on the whole unbounded derived category.

**Stacks 0D6H is not the route.** The alternative reference the source gives, Stacks 0D6H, is
carried by
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/LerayForUnboundedSections.lean`
only in its clause about sections over an *object* of the target site, and only for a morphism of
ringed *sites* — one presented by a continuous functor between the underlying sites. The
augmentation of a hypercovering is not of that shape: it is presented by a cocontinuous functor
out of the total site, and there is no functor `C ⥤ (C/K)_total` to present it the other way. That
shape is what the proof there uses — the underived identity `Γ(V, f_*M) = Γ(u(V), M)` holds *on
the nose* precisely because direct image along a morphism of ringed sites is precomposition with
`u.op`, which is false for the augmentation. What *is* reused from it is the universe-generic
brick
`Stacks.Cohomology.LerayUnbounded.derivedCompIso`, which is exactly how the abelian Stacks 0D8H
is proved in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringDerivedGlobalSections.lean`.

**`RΓ` is `Stacks.DerivedFunctor.totalRightDerived` of the degreewise functor**, the same shape as
`Stacks.Cohomology.DerivedPushforward.derivedPushforward`; in particular `R a_*` *is*
`Stacks.DerivedFunctor.totalRightDerived` of the degreewise direct image, which is what lets
`derivedCompIso` be applied to the pair `(a_*, Γ(C, -))` with no comparison of two models of
`R a_*`.

**Global sections forget the module structure.** The source reads `RΓ(C, E)` in the derived
category of modules over the ring `Γ(C, O_C)` of global functions. Both sides here are instead
read in `D(Ab)`, as in `Stacks.Cohomology.ForgetModule.globalSectionsForgetComparison`, and the
clause string says so. The `Γ(C, O_C)`-linear reading is not out of reach — the
library does have `Stacks.Cohomology.SiteModules.globalSectionsFunctor`, global sections of a
sheaf of modules valued in modules over the global sections of the structure sheaf — but it would
state an isomorphism between objects of two *different* module categories, over `Γ(C, O_C)` and
over `Γ((C/K)_total, O)`, so it additionally needs the restriction of scalars along
`Γ(C, O_C) ⟶ Γ((C/K)_total, O)` and its compatibility with the total right derived functors.
That comparison is not built here.

Global sections are additive because they are a right adjoint, hence preserve binary products. A
global-sections functor exists for every site here because `AddCommGrpCat` has limits of the
shape of the site, which is `CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape`; no
terminal object is involved, which matters because the total site of a hypercovering need not
have one.

## References

* [Stacks Project, Tag 0DA1](https://stacks.math.columbia.edu/tag/0DA1)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0D8H](https://stacks.math.columbia.edu/tag/0D8H)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedTopos

variable (Z : RingedTopos.{u, u, u}) [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Global sections of a sheaf of modules on a ringed topos, with the module structure
forgotten: the underlying abelian sheaf followed by Mathlib's `CategoryTheory.Sheaf.Γ`. This is
the spelling of `Stacks.Cohomology.ForgetModule.moduleGlobalSections`. -/
abbrev moduleGlobalSections :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O) ⥤
      AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O) ⋙
    Sheaf.Γ Z.J AddCommGrpCat.{u}

/-- Global sections of abelian sheaves are additive, being a right adjoint and therefore
preserving binary products. -/
instance additive_abelianGlobalSections : (Sheaf.Γ Z.J AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

instance additive_moduleGlobalSections : (moduleGlobalSections Z).Additive :=
  inferInstanceAs
    ((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O) ⋙
    Sheaf.Γ Z.J AddCommGrpCat.{u})).Additive

/-- `RΓ(C, -)`: the total right derived functor of global sections of sheaves of modules on a
ringed topos, on the unbounded derived category, valued in `D(Ab)`. -/
abbrev derivedModuleGlobalSections :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived (moduleGlobalSections Z)

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

/-! ### The derived factorisation of Stacks 08J6 on sheaves of modules -/

section

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

/-- **Stacks 093Y for a morphism of ringed topoi with invertible structure map.** Degreewise
direct image carries a K-injective complex of sheaves of modules on the source to a K-injective
complex on the target, because `f_*` is the right adjoint of the exact functor `f^*`. -/
theorem isKInjective_pushforwardModules
    (I : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective _).mp
    (_root_.rightAdjoint_preserves_isKInjective _ _ (pullbackAdjPushforwardModules f) I
      ((Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective I).mpr hI))

/-- **The derived half of Stacks 08J6 on sheaves of modules:** granted the underived identity
`Γ(D, f_*M) = Γ(C, M)`, the composition `R f_* ⋙ RΓ(D, -)` is `RΓ(C, -)`.

Both sides are total right derived functors of one and the same functor on the unbounded homotopy
category of sheaves of modules on the source, so they agree by uniqueness of right derived
functors; the input that makes the left hand side a right derived functor at all is
`isKInjective_pushforwardModules`. Only the underived identity is assumed. -/
def derivedGlobalSectionsPushforwardIso
    (hΓ : pushforwardModules f ⋙ RingedTopos.moduleGlobalSections Y ≅
      RingedTopos.moduleGlobalSections X) :
    derivedPushforward (X := X) (Y := Y) f ⋙ RingedTopos.derivedModuleGlobalSections Y ≅
      RingedTopos.derivedModuleGlobalSections X :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIso _ _ _ hΓ (isKInjective_pushforwardModules f)

/-! ### Derived global sections are unchanged by the derived pullback -/

/-- **`RΓ(D, E) = RΓ(C, Lf^*E)` for a morphism of ringed topoi with invertible structure map**,
granted the two inputs of this library's Stacks 0DA0 and the underived identity
`Γ(D, f_*M) = Γ(C, M)`.

The isomorphism is the canonical map `E ⟶ R f_* Lf^* E`, which `hunit` and `hacyclic` make
invertible, followed by the factorisation `R f_* ⋙ RΓ(D, -) ≅ RΓ(C, -)`. It is an isomorphism of
functors on the unbounded derived category, so no boundedness is assumed of `E`. -/
def derivedGlobalSectionsPullbackIso
    (hunit : IsIso (pullbackAdjPushforwardModules f).unit)
    (hacyclic : PullbackComputesDerivedPushforward.{u} f)
    (hΓ : pushforwardModules f ⋙ RingedTopos.moduleGlobalSections Y ≅
      RingedTopos.moduleGlobalSections X) :
    RingedTopos.derivedModuleGlobalSections Y ≅
      (leftDerivedPullbackOfIsIsoFSharp f).functor ⋙
        RingedTopos.derivedModuleGlobalSections X :=
  have := isIso_derivedPullbackPushforwardUnit f hunit hacyclic
  (Functor.leftUnitor (RingedTopos.derivedModuleGlobalSections Y)).symm ≪≫
    Functor.isoWhiskerRight (asIso (derivedPullbackPushforwardUnit f))
      (RingedTopos.derivedModuleGlobalSections Y) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (leftDerivedPullbackOfIsIsoFSharp f).functor
      (derivedGlobalSectionsPushforwardIso f hΓ)

end

end AlgebraicGeometry.RingedToposHom

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

/-- **Stacks 0DA1**, granted the inputs the library does not have. For a site `C` with equalizers
and fibre products, a sheaf of commutative rings `O_C` on it, a hypercovering `K` of `C` and the
ringed augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` of Stacks 0D9W with `O = a⁻¹O_C`,
derived global sections on `C` are derived global sections on the total site of the derived
pullback:

`RΓ(C, E) = RΓ((C/K)_total, La^*E)`.

The statement is an isomorphism of functors on the *unbounded* derived category `D(O_C)` of
sheaves of `O_C`-modules, so it holds at every object `E` with no boundedness assumption, which
is the form the source states.

Three hypotheses are carried. `hunit` and `hacyclic` are the two inputs of this library's
Stacks 0DA0, inherited unchanged from
`isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`: the first is Stacks 0D8E in its
module form, that the underived unit `M ⟶ a_*a^*M` is an isomorphism, and the second is that
`a^*` of a K-injective complex computes `R a_*`. `hΓ` is the underived identity
`Γ(C, a_*M) = Γ((C/K)_total, M)` on which the factorisation of Stacks 08J6 rests; it is
unavailable here for the same reason as its abelian counterpart in this library's Stacks 0D8H,
namely that nothing says the inverse image of a morphism of topoi carries a constant abelian
sheaf to a constant abelian sheaf. The derived content of Stacks 08J6 is *not* assumed: see the
module docstring.

Both sides are read in `D(Ab)`: global sections of a sheaf of modules are taken with the module
structure forgotten, the source's `D(Γ(C, O_C))` reading being unavailable in this library. -/
@[stacks 0DA1 "granted the two inputs of this library's Tag 0DA0 -- the module form of Tag 0D8E \
as hunit and the Ra_*-acyclicity of a^* of a K-injective complex as hacyclic -- and granted the \
underived identity Γ(C, a_*M) = Γ(total, M) of Tag 08J6 as hΓ. Unbounded: the isomorphism is of \
functors on all of D(O_C). Both sides are read in D(Ab), the module structure of global sections \
over Γ(C, O_C) being forgotten"]
def derivedGlobalSectionsPullbackIsoOfHypercovering
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation J H OC).totalRingedHom)
    (hΓ : AlgebraicGeometry.RingedToposHom.pushforwardModules
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom ⋙
        AlgebraicGeometry.RingedTopos.moduleGlobalSections
          (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos ≅
      AlgebraicGeometry.RingedTopos.moduleGlobalSections
        ((hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)) :
    AlgebraicGeometry.RingedTopos.derivedModuleGlobalSections
        (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos ≅
      (AlgebraicGeometry.RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom).functor ⋙
        AlgebraicGeometry.RingedTopos.derivedModuleGlobalSections
          ((hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O) :=
  AlgebraicGeometry.RingedToposHom.derivedGlobalSectionsPullbackIso
    (X := (hypercoveringSituation J H).totalRingedTopos
      (hypercoveringRingedAugmentation J H OC).O)
    (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
    (hypercoveringRingedAugmentation J H OC).totalRingedHom hunit hacyclic hΓ

end Stacks.CategoryTheory.Hypercovering

end
