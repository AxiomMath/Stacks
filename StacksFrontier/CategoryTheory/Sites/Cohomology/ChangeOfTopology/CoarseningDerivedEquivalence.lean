module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedUnitDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalenceRelativeSituation
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The second conclusion of Stacks 07A8: the derived equivalence for a coarsening

Let `C` be a category with two topologies `J' ≤ J`, let `R` be a sheaf of rings for `J` and let
`ε : (C_J, R) ⟶ (C_{J'}, R)` be the comparison morphism of ringed sites. This file proves the
second conclusion of [Stacks, Tag 07A8]: for a weak Serre subcategory `A` of `Mod(R_τ)` whose
objects have vanishing higher `τ`-cohomology on a family which `τ'`-covers every object, derived
pullback and derived pushforward are quasi-inverse equivalences

`D_{A'}(R_τ') ≌ D_A(R_τ)`

between the unbounded derived categories, where `A'` is the image class of the first conclusion.

## Main results

* `Stacks.Cohomology.cofinalCoveringSystemOfBasis`: a cofinal system of coverings of an object,
  all of whose members belong to a class which covers every object.
* `AlgebraicGeometry.RingedSite.isIso_fSharp_auxHomH_coarseningHom` and
  `AlgebraicGeometry.RingedSite.isFlatMapULift_fSharp_auxHomH_coarseningHom`: **`ε` is flat** —
  its structure map in inverse-image form is invertible, which is assumption (1) of
  [Stacks, Tag 0D7W].
* `Stacks.Cohomology.CompareTopologies.exact_map_pushforward_of_vanishing`: **the dévissage
  step** — `ε_*` carries an exact short complex with terms in `A` to an exact short complex.
  This is the hypothesis `hdev` of
  `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`, here discharged.
* `Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE_of_vanishing`: **the first
  conclusion of [Stacks, Tag 07A8]** with that hypothesis gone.
* `Stacks.Cohomology.CompareTopologies.isEquivalence_liftPullbackTopos`: **`ε^*` restricts to an
  equivalence `A' ⟶ A`**, which is assumption (2) of [Stacks, Tag 0D7W].
* `Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE`: **the second
  conclusion of [Stacks, Tag 07A8]**, the equivalence `D_{A'}(R_τ') ≌ D_A(R_τ)`, together with
  `derivedPullbackEquivalenceImageOfLE_functor_comp_ι` and
  `derivedPullbackEquivalenceImageOfLE_inverse_comp_ι` identifying its two functors with the
  restrictions of `Lε^*` and of `Rε_*`.
* `Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfBot`: the same
  equivalence for the coarsening of a topology to the **chaotic** topology, which is the shape
  of the comparison (3) ≃ (4) of [Stacks, Tag 0GZZ]. There `B` is the class of all objects, so
  the only hypothesis left is the vanishing of `H^p_τ(U, F)` for every `U`, every `p > 0` and
  every `F` of `A`.

## The argument

The source deduces the second conclusion from [Stacks, Tag 0D7W], which is available here as
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative`. Its five
assumptions are discharged as follows.

1. **Flatness.** The structure map of `ε` in direct-image form is the identity, so its
   inverse-image form is the counit of the adjunction between `J'`-sheaves and `J`-sheaves of
   commutative rings along the identity functor of `C`. That functor is its own left adjoint and
   is fully faithful, so the counit is invertible by
   `CategoryTheory.Functor.isIso_counit_of_fullyFaithful_leftAdjoint`; an isomorphism of sheaves
   of commutative rings is flat.
2. **The equivalence `A' ⟶ A`.** `ε_*` corestricted to `A'` is an equivalence
   (`Stacks.Cohomology.CompareTopologies.isEquivalence_liftPushforward`), and `ε^*` corestricted
   to `A` is a left adjoint of it, by restricting the adjunction `ε^* ⊣ ε_*` along the two fully
   faithful inclusions. A left adjoint of an equivalence is isomorphic to its quasi-inverse,
   hence is itself an equivalence.
3. **The unit.** This is
   `Stacks.Cohomology.CompareTopologies.isIso_derivedUnit_app_singleFunctor_obj_imageOfLE`.
4. **and 5. The two standing hypotheses.** Both are discharged by the same datum, as in the
   source: the degree bound is `0` on every object of `B`, and the cofinal system of coverings
   attached to an object of `B` consists of the coverings all of whose members lie in `B`. That
   system is cofinal because every object has a covering by members of `B` — for `J` a fortiori
   from the `J'`-covering of the hypothesis — so any covering is refined by binding such a
   covering into each of its members. The vanishing demanded on the members of a distinguished
   covering is then exactly the hypothesis that `H^p_τ(U, F) = 0` for `U` in `B` and `p > 0`.

## The dévissage

Nothing is carried as a hypothesis: the statements below assume exactly what the source does.
In particular the hypothesis `hdev` of
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE` — that `ε_*` preserves exactness of
a short complex with terms in `A` — is proved here rather than assumed, which is also what
removes it from the first conclusion. The module docstring of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/WeakSerreAcrossTopologies.lean`
describes it as needing the long exact sequence of the right derived functors of `ε_*` and a
dévissage of an exact complex into short exact sequences; what it in fact needs is the half of
Leray's acyclicity argument already in the library,
`CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf`, together with the
vanishing `R^pε_*F = 0` of Tag 072W. Those two meet above the import level of
`WeakSerreAcrossTopologies.lean`, which is why the hypothesis is discharged here and not there.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0D7W](https://stacks.math.columbia.edu/tag/0D7W)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6V](https://stacks.math.columbia.edu/tag/0D6V)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.Cohomology

/-! ### A cofinal system of coverings with members in a given class -/

/-- **The coverings of an object all of whose members lie in `B`.** -/
def coveringsWithMembersIn {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Set C) (V : C) : Set (PreZeroHypercover.{u} V) :=
  {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)}

/-- **Binding a covering into each member of a covering is a covering.** -/
theorem sieve₀_bind_mem {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) {V : C}
    (𝒰 : PreZeroHypercover.{u} V) (h𝒰 : 𝒰.sieve₀ ∈ J V)
    (𝒱 : ∀ i, PreZeroHypercover.{u} (𝒰.X i)) (h𝒱 : ∀ i, (𝒱 i).sieve₀ ∈ J (𝒰.X i)) :
    (𝒰.bind 𝒱).sieve₀ ∈ J V := by
  have key := J.bindOfArrows (Z := 𝒰.X) (f := 𝒰.f) (R := fun i ↦ (𝒱 i).presieve₀) h𝒰 h𝒱
  rwa [Presieve.bindOfArrows_ofArrows] at key

/-- **The refinement of a covering by one whose members lie in `B`.** -/
def bindHom {C : Type u} [Category.{u} C] {V : C} (𝒰 : PreZeroHypercover.{u} V)
    (𝒱 : ∀ i, PreZeroHypercover.{u} (𝒰.X i)) : (𝒰.bind 𝒱).Hom 𝒰 where
  s₀ p := p.1
  h₀ p := (𝒱 p.1).f p.2

/-- **The coverings with members in `B` form a cofinal system**, as soon as every object of the
site has a covering whose members lie in `B`: any covering family is refined by the family
obtained by covering each of its members by members of `B`. -/
def cofinalCoveringSystemOfBasis {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (V : C) : CofinalCoveringSystem J V where
  cov := coveringsWithMembersIn J B V
  isCover _ h := h.1
  cofinal 𝒰 h𝒰 := by
    choose 𝒱 h𝒱 hB𝒱 using fun i ↦ hB (𝒰.X i)
    exact ⟨𝒰.bind 𝒱, ⟨sieve₀_bind_mem J 𝒰 h𝒰 𝒱 h𝒱, fun p ↦ hB𝒱 p.1 p.2⟩, ⟨bindHom 𝒰 𝒱⟩⟩

/-- **The one-member covering of an object by its identity is a covering family for every
topology**, the chaotic one included: the sieve it generates is the maximal sieve. -/
theorem sieve₀_singleton_id_mem {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (U : C) : (PreZeroHypercover.singleton.{u} (𝟙 U)).sieve₀ ∈ J U := by
  refine J.superset_covering (fun V g _ ↦ ?_) (J.top_mem U)
  exact ⟨U, g, 𝟙 U, Presieve.ofArrows.mk PUnit.unit, Category.comp_id g⟩

end Stacks.Cohomology

/-! ### Flatness of the coarsening morphism -/

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)

/-- **The structure map of the coarsening morphism `ε` in inverse-image form is invertible.**
The structure map in direct-image form is the identity, so its adjunct is the counit of the
adjunction between `J'`-sheaves and `J`-sheaves of commutative rings along the identity functor
of `C`; the identity functor is its own left adjoint and is fully faithful, so that counit is
invertible.

This is the sentence of the proof of [Stacks, Tag 07A8] that `ε^{-1}𝒪_{τ'} = 𝒪_τ`. -/
theorem isIso_fSharp_auxHomH_coarseningHom :
    IsIso (StacksPullbackFactorization.auxHomH
      (S.coarseningHom h).toRingedToposSiteHom).fSharp := by
  have hcont : (𝟭 S.C).IsContinuous J' S.J := Functor.isContinuous_id_of_le J' S.J h
  have hcounit : IsIso (((𝟭 S.C).sheafAdjunctionContinuous CommRingCat.{u} J' S.J).counit) :=
    Functor.isIso_counit_of_fullyFaithful_leftAdjoint CommRingCat.{u} (𝟭 S.C)
      Adjunction.id J' S.J _
  have heq : (StacksPullbackFactorization.auxHomH
      (S.coarseningHom h).toRingedToposSiteHom).fSharp =
      ((𝟭 S.C).sheafAdjunctionContinuous CommRingCat.{u} J' S.J).counit.app S.O := by
    show (((𝟭 S.C).sheafAdjunctionContinuous CommRingCat.{u} J' S.J).homEquiv _ _).symm
        (𝟙 _) = _
    rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [heq]
  exact NatIso.isIso_app_of_isIso _ _

/-- **The coarsening morphism `ε` is flat**, which is assumption (1) of [Stacks, Tag 0D7W]: its
structure map in inverse-image form is an isomorphism of sheaves of commutative rings, and an
isomorphism of sheaves of commutative rings is flat ([Stacks, Tag 03ER]). -/
theorem isFlatMapULift_fSharp_auxHomH_coarseningHom :
    SheafOfModules.IsFlatMapULift.{u, u, u} (StacksPullbackFactorization.auxHomH
      (S.coarseningHom h).toRingedToposSiteHom).fSharp := by
  have := S.isIso_fSharp_auxHomH_coarseningHom h
  unfold AlgebraicGeometry.SheafOfModules.IsFlatMapULift
  exact SheafOfModules.isFlatMap_of_isIso
    ((AlgebraicGeometry.SheafOfModules.sheafULift _).map (StacksPullbackFactorization.auxHomH
      (S.coarseningHom h).toRingedToposSiteHom).fSharp)

end AlgebraicGeometry.RingedSite

/-! ### The dévissage: `ε_*` preserves exactness on `A` -/

namespace Stacks.Cohomology.CompareTopologies

section Devissage

attribute [local instance] HasDerivedCategory.standard
-- As in `StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicPreservesHomology.lean`: stating
-- `Functor.rightAcyclic` sends instance search after a `HasRightDerivedFunctor` whose default
-- route tries to prove termwise injectivity of an unknown complex, so the cheap instance
-- coming from `EnoughInjectives` is given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v r m

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C} (h : J' ≤ J)
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [EnoughInjectives (_root_.SheafOfModules.{m} R)]
  [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{m})]

/-- `ε_*` preserves finite limits, being the right adjoint of `ε^*`. -/
instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (pushforward.{u, v, r, m} h R) :=
  have : PreservesLimitsOfSize.{0, 0} (pushforward.{u, v, r, m} h R) :=
    (adjunction.{u, v, r, m} h R).rightAdjoint_preservesLimits
  inferInstance

variable (A : ObjectProperty (_root_.SheafOfModules.{m} R)) (B : Set C)
  (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
  (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
    IsZero (Stacks.Cohomology.moduleCohomology R U p F))

include hB hvan in
/-- **Every object of `A` is `ε_*`-acyclic**, under assumptions (2) and (3) of
[Stacks, Tag 07A8]. Right acyclicity for a left exact functor is the vanishing of its positive
right derived functors ([Stacks, Tag 015C]), and that vanishing is Tag 072W for `ε`,
`Stacks.Cohomology.ModuleHigherDirectImage.isZero_rightDerived_ofLE_obj_of_weakSerre`. -/
theorem rightAcyclic_pushforward_of_vanishing
    (F : _root_.SheafOfModules.{m} R) (hF : A F) :
    (pushforward.{u, v, r, m} h R).rightAcyclic F :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived (pushforward.{u, v, r, m} h R) F).2
    fun p hp ↦
      Stacks.Cohomology.ModuleHigherDirectImage.isZero_rightDerived_ofLE_obj_of_weakSerre.{u,
        v, r, m} h R A B hB hvan p hp F hF

include hB hvan in
/-- **`ε_*` carries an exact short complex with terms in `A` to an exact short complex.** This is
the dévissage step of the proof of [Stacks, Tag 07A8] — the hypothesis `hdev` of
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`, here discharged.

Write `T = (X₁ → X₂ → X₃)`, exact at `X₂`, and let `K` be the kernel of `T.f`, which lies in `A`
because a weak Serre subcategory is closed under kernels. Every object of `A` is `ε_*`-acyclic by
`rightAcyclic_pushforward_of_vanishing`, and `T.homology` is a zero object because `T` is exact,
so `ε_*` preserves the left homology of `T` by
`CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf` — the half of Leray's
acyclicity argument which only needs the kernel of `T.toCycles`, and that kernel is `K` because
`T.iCycles` is a monomorphism. A functor preserving the left homology of an exact short complex
carries it to an exact short complex. -/
theorem exact_map_pushforward_of_vanishing [A.IsWeakSerreClass]
    (T : ShortComplex (_root_.SheafOfModules.{m} R)) (hT : T.Exact)
    (h₁ : A T.X₁) (h₂ : A T.X₂) :
    (T.map (pushforward.{u, v, r, m} h R)).Exact := by
  have wk : kernel.ι T.f ≫ T.f = 0 := kernel.condition T.f
  have w : kernel.ι T.f ≫ T.toCycles = 0 := by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp, wk]
  have hk : IsLimit (KernelFork.ofι (kernel.ι T.f) w) :=
    isKernelOfComp T.iCycles T.f (kernelIsKernel T.f) w T.toCycles_i
  have hac := rightAcyclic_pushforward_of_vanishing h R A B hB hvan
  have := ((pushforward.{u, v, r, m} h R).rightAcyclic_cycles_and_preservesLeftHomologyOf T
    (kernel.ι T.f) w hk (hac _ (A.prop_kernel T.f h₁ h₂)) (hac _ h₁)
    (hac _ (A.prop_of_isZero (T.exact_iff_isZero_homology.1 hT)))).2
  exact hT.map_of_preservesLeftHomologyOf _

include hB hvan in
/-- **[Stacks, Tag 07A8], first conclusion, with no hypothesis beyond the source's.** The image
`A'` of `A` under `ε_*` is a weak Serre subcategory of `Mod(R_τ')`. This is
`Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE` with its dévissage hypothesis
`hdev` discharged by `exact_map_pushforward_of_vanishing`. -/
@[stacks 07A8 "the weak Serre subcategory for the coarser topology, with the dévissage step \
discharged"]
theorem isWeakSerreClass_imageOfLE_of_vanishing [A.IsWeakSerreClass] :
    (imageOfLE.{u, v, r, m} h R A).IsWeakSerreClass :=
  isWeakSerreClass_imageOfLE h R A (WeakSerre.isWeakSerre_of_isWeakSerreClass A) B hB hvan
    fun _ _ T hT h₁ h₂ _ ↦ exact_map_pushforward_of_vanishing h R A B hB hvan T hT h₁ h₂

end Devissage

end Stacks.Cohomology.CompareTopologies

/-! ### The equivalence `ε^* : A' ⟶ A` -/

namespace Stacks.Cohomology.CompareTopologies

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)
  [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))

/-- **`ε^*` carries `A'` into `A`**, in the spelling of the inverse image of the morphism of
ringed topoi presented by the coarsening morphism. -/
theorem prop_pullbackTopos_obj_imageOfLE (hA : A.IsClosedUnderIsomorphisms)
    {N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h)}
    (hN : imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A N) :
    A ((S.coarseningHom h).toRingedToposSiteHom.pullbackTopos.obj N) :=
  hA.of_iso ((S.pullbackToposCoarseningHomIso h).app N).symm
    (prop_pullback_obj h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A hA hN)

/-- **The adjunction `ε^* ⊣ ε_*` restricted to `A'` and `A`.** Both functors preserve the two
classes — `ε^*` by `prop_pullbackTopos_obj_imageOfLE` and `ε_*` by the definition of `A'` — and
the two inclusions are fully faithful. -/
def liftPullbackToposAdjLiftPushforwardTopos (hA : A.IsClosedUnderIsomorphisms) :
    A.lift ((imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A).ι ⋙
        (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos)
        (fun N ↦ prop_pullbackTopos_obj_imageOfLE S h A hA N.property) ⊣
      (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A).lift
        (A.ι ⋙ (S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos)
        (fun M ↦ imageOfLE_pushforward_obj h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A
          M.property) :=
  (S.coarseningHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.restrictFullyFaithful
    (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A).fullyFaithfulι A.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- **`ε^*` corestricted to `A` is an equivalence `A' ⟶ A`**, which is assumption (2) of
[Stacks, Tag 0D7W] for the coarsening morphism `ε`.

`ε_*` corestricted to `A'` is an equivalence
(`Stacks.Cohomology.CompareTopologies.isEquivalence_liftPushforward`), and the restriction of
the adjunction `ε^* ⊣ ε_*` exhibits the corestriction of `ε^*` as a left adjoint of it; a left
adjoint of an equivalence is isomorphic to its quasi-inverse, hence is an equivalence. -/
theorem isEquivalence_liftPullbackTopos (hA : A.IsClosedUnderIsomorphisms) :
    (A.lift ((imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A).ι ⋙
      (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos)
      (fun N ↦ prop_pullbackTopos_obj_imageOfLE S h A hA N.property)).IsEquivalence := by
  have hG := isEquivalence_liftPushforward h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A
  exact Functor.isEquivalence_of_iso (Adjunction.leftAdjointUniq
    (@Functor.asEquivalence _ _ _ _ _ hG).symm.toAdjunction
    (liftPullbackToposAdjLiftPushforwardTopos S h A hA))

/-! ### The second conclusion of Stacks 07A8 -/

section Equivalence

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.CohomologicalDescent in
/-- **[Stacks, Tag 07A8], second conclusion.** Let `J' ≤ S.J` be two topologies on the category
of a ringed site `S`, so that the identity functor of that category is the comparison morphism
of ringed sites `ε : (C_τ, 𝒪_τ) ⟶ (C_τ', 𝒪_τ')`. Let `A` be a weak Serre subcategory of
`Mod(𝒪_τ)` and let `B` be a set of objects such that every object has a `τ'`-covering by members
of `B` and `H^p_τ(U, F)` vanishes for `U` in `B`, `p > 0` and `F` in `A`. Then derived pullback
and derived pushforward are quasi-inverse equivalences of the unbounded derived categories

`D_{A'}(𝒪_τ') ≌ D_A(𝒪_τ)`,

where `A'` is the image class of the first conclusion,
`Stacks.Cohomology.CompareTopologies.imageOfLE`.

The five assumptions of [Stacks, Tag 0D7W] are discharged as described in the module docstring.
Nothing is carried: the hypotheses above are exactly the source's own, the dévissage hypothesis
`hdev` of `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE` being proved rather than
assumed, as `exact_map_pushforward_of_vanishing`. -/
@[stacks 07A8 "the equivalence of derived categories given by ε^* and Rε_*"]
def derivedPullbackEquivalenceImageOfLE
    [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
    [EnoughInjectives (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h))]
    [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    [A.IsWeakSerreClass] (B : Set S.C)
    (hB : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : S.C, B U → ∀ p : ℕ, 0 < p →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O), A F →
      IsZero (Stacks.Cohomology.moduleCohomology
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U p F)) :
    (DerivedCategoryB.derivedCategoryB
      (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  haveI hAiso : A.IsClosedUnderIsomorphisms := inferInstance
  -- The `Abelian` instance of the target category is found at the `ringSheaf (S.ofLe h).O`
  -- spelling; the two spellings of the sheaf of rings agree definitionally but not
  -- syntactically, so instance search needs the ascription.
  haveI hA' : @ObjectProperty.IsWeakSerreClass
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) _ _
      (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A) :=
    isWeakSerreClass_imageOfLE_of_vanishing h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A B
      hB hvan
  letI hBJ : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
      𝒰.sieve₀ ∈ S.J U ∧ ∀ i, B (𝒰.X i) := fun U ↦
    ⟨(hB U).choose, h U (hB U).choose_spec.1, (hB U).choose_spec.2⟩
  haveI := hA'
  derivedPullbackEquivalenceUnboundedRelative (S.coarseningHom h)
    (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h) A
    (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)
    (fun _ hM ↦ prop_pullbackTopos_obj_imageOfLE S h A hAiso hM)
    (isEquivalence_liftPullbackTopos S h A hAiso)
    B hBJ (fun _ _ ↦ 0)
    (fun V _ ↦ Stacks.Cohomology.cofinalCoveringSystemOfBasis S.J B hBJ V)
    (fun _ _ _ h𝒰 i p hp F hF ↦ hvan _ (h𝒰.2 i) p (by exact_mod_cast hp) F hF)
    B hB (fun _ _ ↦ 0)
    (fun V _ ↦ Stacks.Cohomology.cofinalCoveringSystemOfBasis J' B hB V)
    (fun _ _ _ h𝒰 i p hp F hF ↦ hvan _ (h𝒰.2 i) p (by exact_mod_cast hp) F hF)
    (fun _ hM ↦ isIso_derivedUnit_app_singleFunctor_obj_imageOfLE S h A hAiso B hB hvan _ hM)

variable [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
  [EnoughInjectives (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h))]
  [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [A.IsWeakSerreClass] (B : Set S.C)
  (hB : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
  (hvan : ∀ U : S.C, B U → ∀ p : ℕ, 0 < p →
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O), A F →
    IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U p F))

/-- **The equivalence of [Stacks, Tag 07A8] is given by `ε^*`**: its forward functor, followed by
the inclusion of `D_A(𝒪_τ)` into `D(𝒪_τ)`, is the inclusion of `D_{A'}(𝒪_τ')` followed by the
derived pullback `Lε^* = ε^*`. -/
@[stacks 07A8 "the forward functor of the equivalence is the derived pullback"]
theorem derivedPullbackEquivalenceImageOfLE_functor_comp_ι :
    letI : (pullbackOnHomotopy (S.coarseningHom h).toRingedToposSiteHom).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).ringedTopos.O))
          (ComplexShape.up ℤ)) :=
      S.hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom h
    (derivedPullbackEquivalenceImageOfLE S h A B hB hvan).functor ⋙
        (DerivedCategoryB.derivedCategoryB A).ι =
      (DerivedCategoryB.derivedCategoryB
        (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
        derivedPullback (S.coarseningHom h).toRingedToposSiteHom :=
  rfl

/-- **The quasi-inverse of the equivalence of [Stacks, Tag 07A8] is `Rε_*`**: it, followed by the
inclusion of `D_{A'}(𝒪_τ')` into `D(𝒪_τ')`, is the inclusion of `D_A(𝒪_τ)` followed by the
derived pushforward `Rε_*`. -/
@[stacks 07A8 "the quasi-inverse of the equivalence is the derived pushforward"]
theorem derivedPullbackEquivalenceImageOfLE_inverse_comp_ι :
    (derivedPullbackEquivalenceImageOfLE S h A B hB hvan).inverse ⋙
        (DerivedCategoryB.derivedCategoryB
          (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι =
      (DerivedCategoryB.derivedCategoryB A).ι ⋙
        derivedPushforward (S.coarseningHom h).toRingedToposSiteHom :=
  rfl

end Equivalence

section Chaotic

attribute [local instance] HasDerivedCategory.standard

/-- **The derived equivalence of [Stacks, Tag 07A8] for the coarsening to the chaotic
topology**, which is the shape of the comparison (3) ≃ (4) of [Stacks, Tag 0GZZ]: reading a
ringed site with the chaotic topology, for which every presheaf is a sheaf, is a coarsening, so
the equivalence applies to it with `B` the class of *all* objects. What is then asked of `A` is
that `H^p_τ(U, F)` vanish for every object `U`, every `p > 0` and every `F` of `A` — for the
affine site of a scheme and `A` the quasi-coherent modules, Serre's vanishing on an affine.

No tag is attached: this is a special case of [Stacks, Tag 07A8], not the tag itself, and it is
not the whole of any numbered clause of [Stacks, Tag 0GZZ] either, the identification of the two
subcategories with (3) and (4) of that tag not being made here. -/
def derivedPullbackEquivalenceImageOfBot (S : RingedSite.{u, u, u})
    [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (⊥ : GrothendieckTopology S.C) AddCommGrpCat.{u}]
    [(⊥ : GrothendieckTopology S.C).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
    [EnoughInjectives (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE
        (bot_le : (⊥ : GrothendieckTopology S.C) ≤ S.J)))]
    [(⊥ : GrothendieckTopology S.C).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
    [A.IsWeakSerreClass]
    (hvan : ∀ (U : S.C) (p : ℕ), 0 < p →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O), A F →
      IsZero (Stacks.Cohomology.moduleCohomology
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U p F)) :
    (DerivedCategoryB.derivedCategoryB (imageOfLE
        (bot_le : (⊥ : GrothendieckTopology S.C) ≤ S.J)
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  derivedPullbackEquivalenceImageOfLE S bot_le A Set.univ
    (fun U ↦ ⟨PreZeroHypercover.singleton.{u} (𝟙 U),
      Stacks.Cohomology.sieve₀_singleton_id_mem _ U, fun _ ↦ trivial⟩)
    fun U _ p hp F hF ↦ hvan U p hp F hF

end Chaotic

end Stacks.Cohomology.CompareTopologies

end
