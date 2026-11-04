module

public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.BoundedBelowComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Abelian-group-valued sections are acyclic on the pushforward of an injective module sheaf

[Stacks, Tag 01EX] part (2) says that the pushforward of an injective sheaf of modules along a
morphism of ringed spaces is right acyclic for *module*-valued sections over any open of the
target. The comparison of the cohomology of a module sheaf with the cohomology of its direct
image needs that acyclicity for *abelian-group*-valued sections instead: the two cohomologies
are the right derived functors of two functors which are the same functor only after the module
structure is forgotten, module-valued sections on `X` and on `Y` landing in modules over the two
different rings `Γ(X, 𝒪_X)` and `Γ(Y, 𝒪_Y)`.

This file carries the acyclicity across the forgetful functor. The two functors differ by
composition with `forget₂ (ModuleCat Γ(V, 𝒪_Y)) Ab`, which is exact, and right acyclicity
transports along an exact functor as soon as the composite is left exact.

## Main results

* `Stacks.LeraySections.rightAcyclic_of_exact_comp`: right acyclicity for an additive `F`
  implies right acyclicity for a left exact `H` whenever `F ⋙ G ≅ H` with `G` exact.
* `Stacks.LeraySections.rightAcyclic_secF_of_rightAcyclic_evaluation`: the instance of that
  transport taking module-valued sections over an open to `Tag01E3.secF`.
* `Stacks.LeraySections.rightAcyclic_secF_modulePushforward_obj` and
  `Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj`: the resulting acyclicity
  statement for the pushforward of an injective module sheaf along a morphism of ringed spaces,
  respectively of schemes. This is the hypothesis that
  `isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective` of
  `StacksDraft.Ch20.Sec12.Tag01F1Canonical2` asks for, and it is what
  `StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Leray` consumes.

No stacks attribute is attached here: these are the inputs of [Stacks, Tag 01F4], stated in the
shape its proof uses, not that lemma.

## Implementation notes

**The left exactness of `secF` is already available.** An implementation note of
`StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic` records that there is no
instance for `PreservesFiniteLimits (secF R U)` because
`CategoryTheory.Limits.comp_preservesFiniteLimits` is a lemma rather than an instance. That
note is out of date: `Stacks.SectionsExact.preservesFiniteLimits_secF` is exactly that
instance, it is universe-polymorphic in all three of the levels involved, and `infer_instance`
finds it at the scheme spelling `secF X.ringCatSheaf U` with no universe adjustment. Nothing
below needs more than `inferInstance` for it.

**Two indexings of the higher derived functors.** `Functor.rightAcyclic` is phrased through the
`ℤ`-indexed `Functor.rightDerivedPlus`, while
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` — the only statement available that
commutes an exact functor past a right derived functor — is phrased through Mathlib's
`ℕ`-indexed `Functor.rightDerived`. `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`
is the bridge, and it is why the degree is split off as a natural number.

**Instance-search budget.** `Functor.rightAcyclic` carries a `HasRightDerivedFunctor`
hypothesis whose search would try to prove termwise injectivity of an unknown complex, so
each section raises the priority of the cheap instance coming from `EnoughInjectives`, as
`StacksDraft.Ch20.Sec12.Tag01F1Canonical2` does. For the same reason the `Abelian` and
`EnoughInjectives` instances of the module-sheaf categories are recorded locally in the
spellings the statements use.

## References

* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe v v' v'' u u' u''

namespace Stacks.LeraySections

/-! ### Transport of right acyclicity along an exact functor -/

section Transport

-- As in `StacksDraft.Ch20.Sec12.Tag01F1Canonical2`: `Functor.rightAcyclic` mentions
-- `HasRightDerivedFunctor`, whose instance search would otherwise try to prove termwise
-- injectivity of an unknown complex, so the cheap instance coming from `EnoughInjectives`
-- is given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} {B : Type u'} {D : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasDerivedCategory B] [HasDerivedCategory D] [EnoughInjectives A]

/-- **Right acyclicity transports along an exact functor.** Let `F : 𝒜 ⥤ ℬ` be additive, let
`G : ℬ ⥤ 𝒟` be additive and exact, and let `H : 𝒜 ⥤ 𝒟` be additive and left exact with
`F ⋙ G ≅ H`. If an object is right acyclic for `F` then it is right acyclic for `H`.

Only `H` is required to be left exact. Acyclicity for `F` is unpacked by part (1) of
[Stacks, Tag 015C], which needs no left exactness, and repacked for `H` by part (2), which
does. In between, `G` applied to the vanishing higher derived functors of `F` gives the
vanishing higher derived functors of `H`, by
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`. -/
theorem rightAcyclic_of_exact_comp [HasDerivedCategory A]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    [G.PreservesHomology] [PreservesFiniteLimits H] (e : F ⋙ G ≅ H) {M : A}
    (hM : F.rightAcyclic M) : H.rightAcyclic M := by
  have h := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F M).1.mp hM).2
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus H M).2 inferInstance]
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff H hn M]
  exact (Functor.map_isZero G
      ((Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff F hn M).1 (h i hi))).of_iso
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).app M).symm

end Transport

/-! ### Abelian-group-valued sections of the pushforward of an injective -/

section Sections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {Z : Type u} [TopologicalSpace Z] (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- Module-valued sections over an open form an additive functor. -/
local instance evaluation_additive (U : Opens Z) :
    (SheafOfModules.evaluation R (op U)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- **Right acyclicity for module-valued sections is right acyclicity for
abelian-group-valued sections.** `secF R U` is module-valued sections over `U` followed by
forgetting the module structure, and that forgetful functor is exact, so
`Stacks.LeraySections.rightAcyclic_of_exact_comp` applies; the left exactness of `secF R U`
it needs is `Stacks.SectionsExact.preservesFiniteLimits_secF`. -/
theorem rightAcyclic_secF_of_rightAcyclic_evaluation (U : Opens Z) {M : SheafOfModules.{u} R}
    (hM : (SheafOfModules.evaluation R (op U)).rightAcyclic M) : (secF R U).rightAcyclic M :=
  rightAcyclic_of_exact_comp _ _ _
    (Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso R U) hM

end Sections

/-! ### The acyclicity input of Stacks 01EX for abelian-group-valued sections -/

section Pushforward

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Module sheaves on a ringed space form an abelian category with enough injectives, and so do
-- module sheaves on a scheme. Both facts are found by search, but only after a search long
-- enough that the statements of this section time out at the default `synthInstance` budget,
-- so they are registered here at the two spellings those statements use:
-- `structureSheafRing` and `AlgebraicGeometry.Scheme.ringCatSheaf`.
attribute [local instance] _root_.Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-- **The acyclicity input of [Stacks, Tag 01EX] for abelian-group-valued sections.** The
pushforward of an injective sheaf of modules along a morphism of ringed spaces is right acyclic
for `Γ(V, -) : Mod(𝒪_Y) ⥤ Ab` over every open `V` of the target.

[Stacks, Tag 01EX] part (2) supplies this for *module*-valued sections; this is the form that
[Stacks, Tag 015M] asks of the pair (pushforward, global sections) when the sections are valued
in abelian groups, which is the only common target the two sides of the comparison have. -/
theorem rightAcyclic_secF_modulePushforward_obj {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) (I : SheafOfModules.{u} (structureSheafRing X)) (hI : Injective I) :
    (secF (structureSheafRing Y) V).rightAcyclic ((modulePushforward f).obj I) :=
  rightAcyclic_secF_of_rightAcyclic_evaluation (structureSheafRing Y) V
    (Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj f V I hI)

/-- The same statement for a morphism of schemes. Every identification involved is `rfl`, by
`Stacks.SchemeCohomology.modulePushforward_hom`. -/
theorem rightAcyclic_secF_schemePushforward_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) (I : X.Modules) (hI : Injective I) :
    (secF Y.ringCatSheaf V).rightAcyclic ((Scheme.Modules.pushforward f).obj I) :=
  rightAcyclic_secF_modulePushforward_obj (Stacks.SchemeCohomology.hom f) V I hI

end Pushforward

end Stacks.LeraySections

end
