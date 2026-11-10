module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# Cohomological descent for hypercoverings: modules

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it and let `K` be a hypercovering. The total site `(C/K)_total` carries the pulled-back
structure sheaf `O = a⁻¹O_C` and the augmentation becomes a morphism of ringed topoi
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)`. Stacks 0DA0 asserts that for `E` in the unbounded
derived category `D(O_C)` the map

`E ⟶ R a_* L a^* E`

is an isomorphism.

## The shape of what is proved

The source's proof is a two-line reduction: since `a⁻¹O_C = O` one has `La^* = a^* = a⁻¹`, the
derived direct image of modules agrees with that of abelian sheaves by Stacks 0D6J, and the
assertion is Stacks 0DA0's abelian counterpart Stacks 0D8G. Neither of the two steps is
available unconditionally in this library:

* the clause of Stacks 0D6J about the unbounded derived direct image along a morphism of ringed
  sites is explicitly *not* carried by the module
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure`,
  which has only the two sections clauses; and
* `Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering`,
  this library's Stacks 0D8G, is itself conditional on two inputs — Stacks 0D8E in its abelian
  form and the `Ra_*`-acyclicity of `a⁻¹` of a K-injective complex.

So the reduction is not taken. Instead the source's *first* observation, `a^* = a⁻¹`, is used
directly on sheaves of modules, and the argument of Stacks 0D8G is carried out one level up, for
`Mod(O)` in place of `Ab(C_total)`. The result is the module statement of Stacks 0DA0 carrying
exactly the two hypotheses that Stacks 0D8G carries, in their module form, and **nothing else**:
no form of Stacks 0D6J is used, and no K-flat machinery (Stacks 06YY, 0G6R, 05VD) is used
either, because the structure map of `a` is invertible and therefore `a^*` is exact.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.leftDerivedPullbackOfIsIsoFSharp`: for a morphism of ringed
  topoi whose structure map is invertible, the Stacks 06YY datum that Stacks 07A6 consumes, with
  the class of *all* complexes as resolving class. `La^*` is then the degreewise pullback.
* `AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp`: the conclusion of
  Stacks 07A6 for such a morphism, `La^* ⊣ Ra_*`, with no deferred input.
* `AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit`: the map `E ⟶ Ra_*La^*E`,
  the unit of that adjunction.
* `AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward`: the module form of the
  second input of Stacks 0D8G, that `a^*` of a K-injective complex computes `Ra_*`.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringRingedAugmentation`: the ringed augmentation
  `a : (Sh((C/K)_total), a⁻¹O_C) ⟶ (Sh(C), O_C)` of a hypercovering of a site with equalizers
  and fibre products.

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp` and
  `.pullbackModules_preservesFiniteColimits_of_adjunction`: **pullback of sheaves of modules
  along a morphism of ringed topoi with invertible structure map is exact.** This is the
  source's `a^* = a⁻¹`.
* `AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit`: the map
  `E ⟶ Ra_*La^*E` is an isomorphism, granted that the underived unit `M ⟶ a_*a^*M` is one and
  that `a^*` of a K-injective complex computes `Ra_*`.
* `Stacks.CategoryTheory.Hypercovering.isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`:
  **Stacks 0DA0** with those two hypotheses, for the ringed augmentation of a hypercovering.
* `isIso_derivedPullbackPushforwardUnit_app_of_hypercovering_over`, in that same namespace:
  **Stacks 0DA5**, the same statement for a hypercovering of an object `X`, over the slice site
  `C/X` with `O_X = O_C|_{C/X}`. It carries the same two hypotheses, and needs only fibre
  products on `C`, the slice site having all finite limits.

## Implementation notes

*Why `a^*` is exact.* The structure sheaf of the total site is `a⁻¹O_C`, taken with the unit of
`a⁻¹ ⊣ a_*` as structure map, so the inverse-image form of that map is the identity
(`CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentation_fSharpInverseImage`).
Invertibility of the structure map makes
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso` available: the underlying sheaf
of sets of `a^*M` is `a⁻¹` of the underlying sheaf of `M`, naturally in `M`. The topos inverse
image is left exact, and the underlying-sheaf functor on sheaves of modules preserves finite
limits and reflects isomorphisms, hence reflects finite limits; right exactness is free, `a^*`
being a left adjoint. This is the same argument as
`CategoryTheory.SimplicialSiteSituation.componentPullbackModules_preservesFiniteLimits`, there
made for the component inclusions `g_n` and here for an arbitrary morphism with invertible
structure map.

*Why no K-flat machinery enters.* `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback` is
the bundle in which Stacks 06YY is expected to supply `La^*`: a resolving class, the existence
of resolutions in it, and the fact that degreewise pullback inverts quasi-isomorphisms between
its objects. For an exact `a^*` the class of *all* complexes does all three — every complex is
its own resolution, and degreewise pullback inverts every quasi-isomorphism by
`Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso`. So
`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunction`, which is Stacks
07A6 relative to that bundle, becomes unconditional here. This is the module analogue of the
`⊤`-resolution device used for the abelian inverse image in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean`.

*The reduction to K-injective complexes* is
`Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives`, available because sheaves of
modules on a ringed topos form a Grothendieck abelian category. That is why the hypothesis
`hacyclic` is stated at K-injective complexes while the conclusion holds for every object of
`D(O_C)`, with no boundedness assumption.

*The two hypotheses are the two of Stacks 0D8G, in module form.* `hunit` is Stacks 0D8E for
modules, that the underived unit `M ⟶ a_*a^*M` is an isomorphism; `hacyclic` is the module form
of the derived content of the source's computation of `Ra_*a^*` on an injective sheaf, which
rests on the spectral sequence of Stacks 0D7A that this library does not build. Neither is used
by the construction of `La^*`, of `Ra_*`, of their adjunction or of its unit: those are
unconditional.

*The hypercovering is the one of Stacks 0D8G.* The simplicial-site situation and the
augmentation are `Stacks.CategoryTheory.Hypercovering.hypercoveringSituation` and
`.hypercoveringAugmentation`, the same two that this library's Stacks 0D8G is stated for, and
the ringed augmentation on top of them is
`CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentation`, the Stacks 0D9W reading
in which the structure sheaf of the total site is `a⁻¹O_C`. The hypotheses that the site has
equalizers and fibre products appear as the instance arguments `[HasEqualizers C]` and
`[HasPullbacks C]`, which is what makes
`Stacks.CategoryTheory.Hypercovering.HypercoveringOfTerminal` well formed at all.

## References

* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedToposHom

/-! ### The derived pullback along a morphism with invertible structure map

For a morphism of ringed topoi `f` whose structure map `f♯ : f⁻¹O_D ⟶ O_C` is invertible the
pullback of sheaves of modules is exact, so `Lf^*` is the degreewise pullback and the derived
adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6 needs no K-flat input. -/

section ExactPullback

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

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Pullback of sheaves of modules along a morphism of ringed topoi with invertible structure
map is left exact.** The structure map being invertible, the underlying sheaf of sets of `f^*M`
is `f⁻¹` of the underlying sheaf of `M`, naturally in `M`, by `pullbackUnderlyingIsoOfIsIso`;
the inverse image is left exact because `f` is a morphism of topoi, and the underlying-sheaf
functor on sheaves of modules preserves finite limits and reflects isomorphisms, hence reflects
finite limits.

This is the source's observation `a^* = a⁻¹` for the ringed augmentation of Stacks 0D9W. -/
@[sga "4 IV 13.7" "partial"]
theorem pullbackModules_preservesFiniteLimits_of_isIso_fSharp :
    PreservesFiniteLimits f.toModulesHom.pullbackModules := by
  have :=
    Sheaf.moduleSheafFunctor_preservesFiniteLimits (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  have :=
    Sheaf.moduleSheafFunctor_preservesFiniteLimits (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have := f.toToposHom.preservesFiniteLimits
  have : PreservesFiniteLimits (f.toModulesHom.pullbackModules ⋙
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    preservesFiniteLimits_of_natIso (pullbackUnderlyingIsoOfIsIso.{u} f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsIso f.fSharpInverseImage] in
/-- **Pullback of sheaves of modules along a morphism of ringed topoi is right exact**, being a
left adjoint. This is the finite case of Stacks 03DC part (2). -/
theorem pullbackModules_preservesFiniteColimits_of_adjunction :
    PreservesFiniteColimits f.toModulesHom.pullbackModules :=
  have := RingedToposHom.pullbackModules_preservesColimitsOfSize.{_, _, _, _, _, _, u, u} f
  PreservesColimitsOfSize.preservesFiniteColimits _

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

/-- Every complex is its own resolution by the class of all objects, so that class resolves the
quasi-isomorphisms. -/
theorem exists_top_resolution
    (M : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ)) :
    ∃ (N : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ)) (_ : (⊤ : ObjectProperty _) N) (s : N ⟶ M), targetQuasiIso Y s :=
  ⟨M, trivial, 𝟙 M, MorphismProperty.id_mem _ _⟩

/-- Degreewise pullback inverts every quasi-isomorphism, `f^*` being exact. -/
theorem pullbackOnHomotopy_inverts_quasiIso
    {M N : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (ComplexShape.up ℤ)} (s : M ⟶ N) (hs : targetQuasiIso Y s) :
    IsIso ((pullbackOnHomotopy f).map s) :=
  Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
    (f.toModulesHom.pullbackModules) _ hs

/-- **The Stacks 06YY datum for a morphism with invertible structure map**, with the class of
*all* complexes as resolving class: `f^*` being exact, every complex resolves itself and
degreewise pullback inverts every quasi-isomorphism. So `Lf^*` is the degreewise pullback, and
no K-flat complex enters. -/
def leftDerivedPullbackOfIsIsoFSharp : LeftDerivedPullback f :=
  LeftDerivedPullback.ofResolving f ⊤ (exists_top_resolution (Y := Y))
    (fun s hs _ _ => pullbackOnHomotopy_inverts_quasiIso f s hs)

/-- **Stacks 07A6 for a morphism of ringed topoi with invertible structure map**, with no
deferred input: `Lf^*` is left adjoint to `Rf_*` on the unbounded derived categories of sheaves
of modules.

No `@[stacks 07A6]` attribute is placed here, by the convention of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionViaFlatPullback.lean`:
invertibility of the structure map is a hypothesis the source does not have, Stacks 07A6 being
stated for an arbitrary morphism of ringed topoi. -/
def derivedAdjunctionOfIsIsoFSharp :
    (leftDerivedPullbackOfIsIsoFSharp f).functor ⊣ derivedPushforward (X := X) (Y := Y) f :=
  derivedPullbackPushforwardAdjunction f (leftDerivedPullbackOfIsIsoFSharp f)

/-- The canonical map `E ⟶ Rf_*Lf^*E`, the unit of the derived adjunction. -/
abbrev derivedPullbackPushforwardUnit :
    𝟭 (DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) ⟶
      (leftDerivedPullbackOfIsIsoFSharp f).functor ⋙
        derivedPushforward (X := X) (Y := Y) f :=
  (derivedAdjunctionOfIsIsoFSharp f).unit

/-- The module form of the second input of Stacks 0D8G: for a K-injective complex `I` of
`O_D`-modules the degreewise pullback `f^*I` computes the derived direct image, that is, the
canonical map `f_*f^*I ⟶ Rf_*f^*I` is an isomorphism. -/
def PullbackComputesDerivedPushforward : Prop :=
  ∀ I : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) ℤ,
    I.IsKInjective →
    IsIso (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso X)).app
      ((pullbackMapHomotopy f).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
          (ComplexShape.up ℤ)).obj I)))

/-- **The canonical map `E ⟶ Rf_*Lf^*E` is an isomorphism**, granted two inputs: that the
underived unit `M ⟶ f_*f^*M` of Stacks 03D7 is an isomorphism, and that `f^*` of a K-injective
complex computes `Rf_*`.

The reduction is the one of Stacks 0D8G, carried out for sheaves of modules. A natural
transformation out of the unbounded derived category is invertible as soon as it is invertible
at the K-injective complexes; there the derived unit is, after the comparison maps of `Lf^*` and
`Rf_*`, the degreewise unit, which is invertible by `hunit` degreewise and `hacyclic` on the
derived side. Neither hypothesis is used by the construction of `Lf^*`, of `Rf_*`, of their
adjunction or of its unit. -/
theorem isIso_derivedPullbackPushforwardUnit
    (hunit : IsIso (pullbackAdjPushforwardModules f).unit)
    (hacyclic : PullbackComputesDerivedPushforward f) :
    IsIso (derivedPullbackPushforwardUnit f) := by
  have := hunit
  refine Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives _ (fun I hI => ?_)
  have := hacyclic I hI
  set M := (HomotopyCategory.quotient
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
    (ComplexShape.up ℤ)).obj I with hM
  have : IsIso ((pullbackAdjPushforwardMapHomotopy f).unit.app M) :=
    Adjunction.isIso_mapHomotopyCategoryAdjunction_unit_app _ _ _
  have hcmp : IsIso ((leftDerivedPullbackOfIsIsoFSharp f).comparison.app M) :=
    (leftDerivedPullbackOfIsIsoFSharp f).isIso_comparison M trivial
  have hfac := derivedPullbackPushforwardAdjunction_unit_fac f
    (leftDerivedPullbackOfIsIsoFSharp f) M
  have hcomp : IsIso ((derivedPullbackPushforwardUnit f).app (DerivedCategory.Qh.obj M) ≫
      (derivedPushforward (X := X) (Y := Y) f).map
        ((leftDerivedPullbackOfIsIsoFSharp f).comparison.app M)) := by
    rw [derivedPullbackPushforwardUnit, derivedAdjunctionOfIsIsoFSharp, hfac]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((derivedPushforward (X := X) (Y := Y) f).map
    ((leftDerivedPullbackOfIsIsoFSharp f).comparison.app M))

end ExactPullback

end AlgebraicGeometry.RingedToposHom

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

/-- **Stacks 0D9W for a hypercovering.** The ringed augmentation
`a : (Sh((C/K)_total), a⁻¹O_C) ⟶ (Sh(C), O_C)` of the total site of a hypercovering of a site
with equalizers and fibre products: the structure sheaf of the total site is the inverse image
of `O_C` and the structure map is the unit of `a⁻¹ ⊣ a_*`, so its inverse-image form is the
identity. The underlying simplicial-site situation and augmentation are those of this library's
Stacks 0D8G. -/
abbrev hypercoveringRingedAugmentation :
    CategoryTheory.SimplicialSiteSituation.RingedAugmentation (hypercoveringSituation J H)
      (CategoryTheory.Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H) :=
  CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentation _ _ _ _ OC

/-- The site of the ringed topos the hypercovering is augmented over is `C` with the topology
generated by `J`. -/
theorem hypercoveringRingedAugmentation_augmentationRingedTopos_J :
    (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.J = J.toGrothendieck :=
  rfl

/-- The structure sheaf of the ringed topos the hypercovering is augmented over is `O_C`. So the
coefficients of the statement below really are the sheaves of `O_C`-modules on `C`. -/
theorem hypercoveringRingedAugmentation_augmentationRingedTopos_O :
    (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.O = OC :=
  rfl

/-- **Stacks 0DA0**, granted the two inputs this library's Stacks 0D8G is granted, in their
module form. Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
commutative rings on it and let `K` be a hypercovering of `C`. With `O = a⁻¹O_C` on the total
site and `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` the ringed augmentation of Stacks 0D9W, the
canonical map

`E ⟶ R a_* L a^* E`

is an isomorphism for every object `E` of the unbounded derived category `D(O_C)` of sheaves of
`O_C`-modules.

`E` is arbitrary: no boundedness is assumed and the coefficients are the full category of
sheaves of modules. `La^*` is the degreewise pullback, which is the source's first observation,
and nothing of Stacks 06YY, 0G6R or 05VD enters.

The two hypotheses are the two of
`Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering`, read
for sheaves of modules instead of abelian sheaves. `hunit` is Stacks 0D8E in its module form,
that the underived unit `M ⟶ a_*a^*M` is an isomorphism; it is not available here because its
proof needs the abelian form of Stacks 0D86, which this library has for sheaves of sets only.
`hacyclic` says that `a^*` of a K-injective complex of `O_C`-modules computes `Ra_*`; it is the
derived content of the source's computation of `Ra_*a^*` by the Čech complex, which rests on the
spectral sequence of Stacks 0D7A that this library does not build. The source's own route — the
abelian statement of Stacks 0D8G together with Stacks 0D6J — would carry the same two
hypotheses through Stacks 0D8G *and* in addition the clause of Stacks 0D6J about the derived
direct image, which this library does not have; so that route is not taken and the count of
deferred inputs is exactly two. -/
@[stacks 0DA0 "granted the module form of Tag 0D8E as hunit and the Ra_*-acyclicity of a^* of a \
K-injective complex as hacyclic -- the two inputs that this library's Tag 0D8G, \
`isIso_derivedAugmentationUnit_app_of_hypercovering`, is itself granted"]
theorem isIso_derivedPullbackPushforwardUnit_app_of_hypercovering
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation J H OC).totalRingedHom)
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.J))
      (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.O))) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).app E) :=
  have := AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit
    (hypercoveringRingedAugmentation J H OC).totalRingedHom hunit hacyclic
  NatIso.isIso_app_of_isIso _ E

section HypercoveringOfObject

variable {X : C} (P : Pretopology C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (O : Sheaf P.toGrothendieck CommRingCat.{u})

omit [HasEqualizers C] in
/-- **Stacks 0DA5.** Let `C` be a site with fibre products, `X` an object of it, `O_C` a sheaf of
rings and `K` a hypercovering of `X`. Writing `O_X = O_C|_{C/X}` and `a` for the augmentation of
the total site of `K` over the slice site `C/X`, the canonical map `E ⟶ Ra_*La^*E` is an
isomorphism for every `E` in the derived category of `O_X`-modules.

The slice site `C/X` has a terminal object and inherits fibre products from `C`, so it has all
finite limits; this is why the source asks only for fibre products on `C` here, where Stacks
0DA0 asks for equalizers as well. The augmentation is the ringed one of Stacks 0D9X, and the two
pinning lemmas `hypercoveringObjectRingedAugmentation_augmentationRingedTopos_J` and `_O` certify
that the coefficients are the sheaves of `O_X`-modules on `C/X`. The hypercovering condition on
`K` is recorded as `hK`, and, exactly as in Stacks 0DA0, it is absorbed into the two deferred
inputs rather than consumed directly. -/
@[stacks 0DA5 "granted the module form of Tag 0D8E as hunit and the Ra_*-acyclicity of a^* of a \
K-injective complex as hacyclic -- the same two inputs this library's Tag 0DA0, \
`isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`, is itself granted"]
theorem isIso_derivedPullbackPushforwardUnit_app_of_hypercovering_over
    (_hK : IsHypercovering P K)
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P K O).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringObjectRingedAugmentation P K O).totalRingedHom)
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringObjectRingedAugmentation P K O).augmentationRingedTopos.J))
      (hypercoveringObjectRingedAugmentation P K O).augmentationRingedTopos.O))) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringObjectRingedAugmentation P K O).totalRingedHom).app E) :=
  have := AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit
    (hypercoveringObjectRingedAugmentation P K O).totalRingedHom hunit hacyclic
  NatIso.isIso_app_of_isIso _ E

end HypercoveringOfObject

end Stacks.CategoryTheory.Hypercovering

end
