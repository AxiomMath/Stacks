module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedUnitDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologiesOfVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalenceRelativeSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful
import StacksCore.Tactic.StacksAttribute

/-!
# The derived categories of a weak Serre subcategory for two topologies

Let `C` be a category carrying two Grothendieck topologies, a finer one `J` (the topology `τ` of
the source) and a coarser one `J' ≤ J` (the topology `τ'`), and let `𝒪` be a sheaf of rings for
`J`, so that the identity functor of `C` presents the comparison morphism of ringed sites

`ε : (C_τ, 𝒪_τ) ⟶ (C_τ', 𝒪_τ')`.

Let `A` be a weak Serre subcategory of `Mod(𝒪_τ)` and let `A'` be its image under `ε_*`.  This
file proves the **second conclusion of Stacks 07A8**: at the source's own four hypotheses the
derived categories of complexes with cohomology in `A` resp. `A'` are equivalent as triangulated
categories,

`D_A(𝒪_τ) ≌ D_{A'}(𝒪_τ')`,

the equivalence being given by `ε^*` and `Rε_*`.

## Main definitions

* `Stacks.Cohomology.CompareTopologies.cofinalCoveringSystemOfSet`: the coverings whose members
  lie in a family `B`, as a cofinal system of coverings of any object, for any topology at least
  as fine as one in which `B` covers everything.
* `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`: the equivalence
  `D_A(𝒪_τ) ≌ D_{A'}(𝒪_τ')`.
* `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLEInverseCommShift`: the shift
  structure of `Lε^*` on its quasi-inverse.

## Main results

* `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE_spec`: **Stacks 07A8**, the
  second conclusion — the equivalence is one of triangulated categories, its functor is `Rε_*`
  and its quasi-inverse is `Lε^*`, which is `ε^*` applied termwise.

Hypotheses (1) and (2) of Stacks 0D7W for `ε` — that `ε` is flat and that `ε^*` corestricts to an
equivalence `A' ≌ A` — are
`AlgebraicGeometry.RingedSite.isFlatMapULift_fSharp_auxHomH_coarseningHom` and
`Stacks.Cohomology.CompareTopologies.isEquivalence_liftPullbackTopos`.

The equivalence is the one of Stacks 0D7W read backwards, so its functor is the restriction of
`Rε_*` and its quasi-inverse the restriction of `Lε^*`; both identifications hold by `rfl`, from
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative_inverse` and
`..._functor`.  The quasi-inverse is a triangulated functor because `Lε^*` is (Stacks 06YY) and
`D_A(𝒪_τ)` is a full triangulated subcategory of `D(𝒪_τ)`; the functor of an equivalence whose
quasi-inverse is triangulated is triangulated for the transported shift structure.  As `ε^*` is
exact, `Lε^*` is `ε^*` applied termwise
(`Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso`).

## The argument

The source obtains the equivalence from Stacks 0D7W, applied to `ε`, to `A` and to `A'`, and the
whole of this file is the verification of that tag's five hypotheses for `ε`.

Hypothesis (1), flatness, is
`AlgebraicGeometry.RingedSite.isFlatMapULift_fSharp_auxHomH_coarseningHom`, and hypothesis (2),
that `ε^*` induces an equivalence `A' ⟶ A`, is
`Stacks.Cohomology.CompareTopologies.isEquivalence_liftPullbackTopos`.

Hypothesis (3), that `ℱ' ⟶ Rε_*ε^*ℱ'` is invertible on `A'`, is
`Stacks.Cohomology.CompareTopologies.isIso_derivedUnit_app_singleFunctor_obj_imageOfLE`, and
rests on assumptions (3) and (4) of 07A8 through Stacks 072W.

Hypotheses (4) and (5), the standing hypothesis of Stacks 0D6R for the source site and the
relative hypothesis of Stacks 0D6V for `ε`, are what the source disposes of by remarking that
"since every object has a `τ'`-covering by objects of `B`, a fortiori every object has a
`τ`-covering by objects of `B`".  Both need, besides that covering statement, a cofinal system of
coverings of each member of `B` on whose members the cohomology of the modules of `A` vanishes
above a bound.  The system is `cofinalCoveringSystemOfSet`: the coverings all of whose members
lie in `B`.  It is cofinal because any covering can be refined by covering each of its members by
members of `B`, which is assumption (3); the bound is `0` and the vanishing on the members is
assumption (4) verbatim.  For the relative hypothesis the cohomology is computed over the image
`ε(V'_i)` of a member of a covering of the coarse site, and that image is `V'_i` itself, the
underlying functor of `ε` being the identity.

## Hypotheses

The four hypotheses are exactly the source's: `A.IsWeakSerreClass` is (2), `hB` is (3) and
`hvan` is (4), and (1) — that every object of `A` is a sheaf for the finer topology — is built
into the shape of the statement, `A` being a class of `J`-sheaves of modules to begin with, as it
already is for the first conclusion.  Nothing else about `C`, `𝒪`, `A` or `B` is assumed: the
existence of sheafification for both topologies, its description by locally bijective
morphisms, and the existence of enough injectives in both categories of sheaves of modules are
all instances at the size of an `AlgebraicGeometry.RingedSite`, whose objects, morphisms and
sections share one universe, which is the size at which Stacks 0D7W is available.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0D7W](https://stacks.math.columbia.edu/tag/0D7W)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6V](https://stacks.math.columbia.edu/tag/0D6V)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.Cohomology.CompareTopologies

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-! ### The cofinal system of coverings by members of a family -/

section Coverings

variable {C : Type u} [Category.{u} C]

/-- **The coverings whose members lie in `B` form a cofinal system of coverings of every
object.**  Here `B` is a family of objects which covers every object of `C` for some topology `K`
no finer than `J`, and the system is taken in `J`.

Cofinality is the source's own remark: given a `J`-covering of `V`, cover each of its members by
members of `B` — possible by the hypothesis on `K` — and the resulting composite family is a
`J`-covering of `V` by members of `B` refining the given one.  That it is a covering is the
transitivity axiom of a Grothendieck topology. -/
def cofinalCoveringSystemOfSet {K J : GrothendieckTopology C} (hKJ : K ≤ J) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ K U ∧ ∀ i, B (𝒰.X i))
    (V : C) : Stacks.Cohomology.CofinalCoveringSystem J V where
  cov 𝒰 := 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)
  isCover _ h := h.1
  cofinal 𝒰 h𝒰 := by
    choose 𝒱 h𝒱 hB𝒱 using fun i : 𝒰.I₀ ↦ hB (𝒰.X i)
    refine ⟨𝒰.bind 𝒱, ⟨?_, fun ij ↦ hB𝒱 ij.1 ij.2⟩,
      ⟨{ s₀ := Sigma.fst, h₀ := fun ij ↦ (𝒱 ij.1).f ij.2, w₀ := fun _ ↦ rfl }⟩⟩
    refine J.transitive h𝒰 _ fun Y g hg ↦ ?_
    obtain ⟨Z, a, b, hb, rfl⟩ := hg
    obtain ⟨i⟩ := hb
    rw [Sieve.pullback_comp]
    refine J.pullback_stable _ (J.superset_covering (fun W k hk ↦ ?_) (hKJ _ (h𝒱 i)))
    obtain ⟨W', c, d, hd, rfl⟩ := hk
    obtain ⟨j⟩ := hd
    have := (𝒰.bind 𝒱).sieve₀.downward_closed ((𝒰.bind 𝒱).sieve₀_f ⟨i, j⟩) c
    simpa [PreZeroHypercover.bind] using this

end Coverings


/-! ### Stacks 07A8, the second conclusion -/

section Derived

variable (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
  [A.IsWeakSerreClass]
  (B : Set S.C)
  (hB : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
  (hvan : ∀ U : S.C, B U → ∀ p : ℕ, 0 < p →
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O), A F →
    IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U p F))

include hB hvan in
/-- **The equivalence of Stacks 07A8.**  Let `J' ≤ J` be two topologies on `C` and let `𝒪` be a
sheaf of rings for the finer topology `J`, so that the identity functor of `C` presents the
comparison morphism of ringed sites `ε : (C_τ, 𝒪_τ) ⟶ (C_τ', 𝒪_τ')`.  Let `A` be a class of
sheaves of `𝒪`-modules for `J` — the source's assumption (1), that every object of `A` is a
sheaf for the finer topology, is this — and let `B` be a set of objects of `C`.  Assume

1. `A` is a weak Serre subcategory of `Mod(𝒪_τ)`,
2. every object of `C` has a `J'`-covering whose members lie in `B`,
3. for every `U` in `B` the cohomology `H^p_τ(U, F)` vanishes for `p > 0` and `F` in `A`.

Then the derived category of complexes of `𝒪_τ`-modules with cohomology in `A` and the derived
category of complexes of `𝒪_τ'`-modules with cohomology in the image class
`A' = ε_*A` are equivalent, the equivalence being given by `ε^*` and `Rε_*`.

This is Stacks 0D7W applied to `ε`; its five hypotheses are discharged as described in the
module documentation.  That it is triangulated and given by `ε^*` and `Rε_*` is
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE_spec`. -/
def derivedEquivalenceImageOfLE :
    (DerivedCategoryB.derivedCategoryB A).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB
        (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
          A)).FullSubcategory := by
  haveI : ObjectProperty.IsWeakSerreClass
      (show ObjectProperty
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).O)) from
        imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A) :=
    isWeakSerreClass_imageOfLE_of_univLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A) B hB hvan
  have hcov : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
      𝒰.sieve₀ ∈ S.J U ∧ ∀ i, B (𝒰.X i) := by
    intro U
    obtain ⟨𝒰, h₁, h₂⟩ := hB U
    exact ⟨𝒰, h _ h₁, h₂⟩
  exact (Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative
    (S.coarseningHom h) (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h) A
    (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)
    (fun _ hN ↦ prop_pullbackTopos_obj_imageOfLE S h A inferInstance hN)
    (isEquivalence_liftPullbackTopos S h A inferInstance)
    B hcov (fun _ _ ↦ 0) (fun V _ ↦ cofinalCoveringSystemOfSet h B hB V)
    (fun _ _ 𝒰 h𝒰 i p hp F hF ↦ hvan (𝒰.X i) (h𝒰.2 i) p (by exact_mod_cast hp) F hF)
    B hB (fun _ _ ↦ 0) (fun V _ ↦ cofinalCoveringSystemOfSet le_rfl B hB V)
    (fun _ _ 𝒰 h𝒰 i p hp F hF ↦ hvan (𝒰.X i) (h𝒰.2 i) p (by exact_mod_cast hp) F hF)
    (fun _ hN ↦ isIso_derivedUnit_app_singleFunctor_obj_imageOfLE S h A inferInstance B hB
      hvan _ hN)).symm

/-- **The functor of the equivalence is `Rε_*`.**  Read in
`D(𝒪_τ')`, the functor of
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE` is the derived pushforward
`Rε_*` restricted to `D_A(𝒪_τ)`.

It holds by `rfl`: the equivalence is
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative` read
backwards, whose quasi-inverse is `Rε_*` by
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative_inverse`. -/
theorem derivedEquivalenceImageOfLE_functor_comp_ι :
    (derivedEquivalenceImageOfLE S h A B hB hvan).functor ⋙
        (DerivedCategoryB.derivedCategoryB
          (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι =
      (DerivedCategoryB.derivedCategoryB A).ι ⋙
        derivedPushforward.{u} (S.coarseningHom h).toRingedToposSiteHom :=
  rfl

/-- **The quasi-inverse of the equivalence is `Lε^*`.**  Read in `D(𝒪_τ)`, the quasi-inverse of
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE` is the derived pullback
`Lε^*` restricted to `D_{A'}(𝒪_τ')`; since `ε^*` is exact, `Lε^*` is `ε^*` degreewise.

It holds by `rfl`, by
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative_functor`. -/
theorem derivedEquivalenceImageOfLE_inverse_comp_ι :
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
      (S.coarseningHom h).toRingedToposSiteHom
    (derivedEquivalenceImageOfLE S h A B hB hvan).inverse ⋙
        (DerivedCategoryB.derivedCategoryB A).ι =
      (DerivedCategoryB.derivedCategoryB
          (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
        derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom :=
  rfl

/-- The shift structure on the restriction of `Lε^*` to `D_{A'}(𝒪_τ')`: that of the inclusion of
the triangulated subcategory followed by that of `Lε^*`, which commutes with the shift as every
left derived functor does. -/
@[instance_reducible]
def derivedPullbackRestrictionCommShift :
    haveI : (DerivedCategoryB.derivedCategoryB
        (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
        B hB hvan)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
      (S.coarseningHom h).toRingedToposSiteHom
    ((DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
        derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom).CommShift ℤ :=
  haveI : (DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
      B hB hvan)
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
    (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
    (S.coarseningHom h).toRingedToposSiteHom
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ (ObjectProperty.commShiftι _)
    (Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift
      (S.coarseningHom h).toRingedToposSiteHom)

/-- The shift structure on the quasi-inverse of
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`: the one transported from the
restriction of `Lε^*` along
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE_inverse_comp_ι`. -/
@[instance_reducible]
def derivedEquivalenceImageOfLEInverseCommShift :
    haveI : (DerivedCategoryB.derivedCategoryB
        (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
        B hB hvan)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
      (S.coarseningHom h).toRingedToposSiteHom
    (derivedEquivalenceImageOfLE S h A B hB hvan).inverse.CommShift ℤ :=
  haveI : (DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
      B hB hvan)
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
    (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
    (S.coarseningHom h).toRingedToposSiteHom
  letI := derivedPullbackRestrictionCommShift S h A B hB hvan
  Functor.CommShift.ofComp (eqToIso (derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan)) ℤ

include hB hvan in
/-- **The equivalence is one of triangulated categories.**  With
the shift structure of `Lε^*` on the quasi-inverse
(`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLEInverseCommShift`) and the
compatible one on the functor, the equivalence
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE` is a triangulated equivalence
between the triangulated subcategories `D_A(𝒪_τ)` and `D_{A'}(𝒪_τ')`, and the identification of
its quasi-inverse with the restriction of `Lε^*`
(`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE_inverse_comp_ι`) commutes with
the shift.

The quasi-inverse is triangulated because `Lε^*` is (Stacks 06YY, through
`Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated`) and `D_A(𝒪_τ)` is a
full triangulated subcategory; the functor of an equivalence whose quasi-inverse is triangulated
is triangulated as well. -/
theorem derivedEquivalenceImageOfLE_isTriangulated :
    haveI : (DerivedCategoryB.derivedCategoryB
        (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
        B hB hvan)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
      (S.coarseningHom h).toRingedToposSiteHom
    letI := derivedPullbackRestrictionCommShift S h A B hB hvan
    letI := derivedEquivalenceImageOfLEInverseCommShift S h A B hB hvan
    letI := (derivedEquivalenceImageOfLE S h A B hB hvan).commShiftFunctor ℤ
    haveI := (derivedEquivalenceImageOfLE S h A B hB hvan).commShift_of_inverse ℤ
    (derivedEquivalenceImageOfLE S h A B hB hvan).IsTriangulated ∧
      NatTrans.CommShift (eqToIso (derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan)).hom
        ℤ := by
  have : (DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
      (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
      B hB hvan)
  let := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
    (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
  let := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
    (S.coarseningHom h).toRingedToposSiteHom
  let := derivedPullbackRestrictionCommShift S h A B hB hvan
  let := derivedEquivalenceImageOfLEInverseCommShift S h A B hB hvan
  let := (derivedEquivalenceImageOfLE S h A B hB hvan).commShiftFunctor ℤ
  have := (derivedEquivalenceImageOfLE S h A B hB hvan).commShift_of_inverse ℤ
  have hcomm : NatTrans.CommShift
      (eqToIso (derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan)).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  let cι : (DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι.CommShift ℤ :=
    ObjectProperty.commShiftι _
  let cL : (derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom).CommShift ℤ :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift
      (S.coarseningHom h).toRingedToposSiteHom
  have tι : (DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι.IsTriangulated :=
    ObjectProperty.instIsTriangulatedFullSubcategoryι _
  have tL : (derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated
      (S.coarseningHom h).toRingedToposSiteHom
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact
        (S.coarseningHom h).toRingedToposSiteHom)
  have hcomp : ((DerivedCategoryB.derivedCategoryB
      (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
        derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom).IsTriangulated :=
    ⟨fun T hT ↦ Pretriangulated.isomorphic_distinguished _
      ((derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom).map_distinguished _
        ((DerivedCategoryB.derivedCategoryB (imageOfLE.{u, u, u, u} h
          (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι.map_distinguished T hT)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ _ cι _ cL).app T)⟩
  have hinv : (derivedEquivalenceImageOfLE S h A B hB hvan).inverse.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right
      (eqToIso (derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan))).2 hcomp
  exact ⟨Equivalence.IsTriangulated.mk'' _ hinv, hcomm⟩

/-- **The quasi-inverse is `ε^*`.**  Since `ε^*` is exact it acts on derived categories
termwise, and the derived pullback `Lε^*` is that functor
(`Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso`); so, read in `D(𝒪_τ)`, the
quasi-inverse of `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE` is `ε^*`
applied termwise to a complex of `D_{A'}(𝒪_τ')`. -/
def derivedEquivalenceImageOfLEInverseCompιIso :
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := Functor.additive_of_preserves_binary_products
      (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos
    (derivedEquivalenceImageOfLE S h A B hB hvan).inverse ⋙
        (DerivedCategoryB.derivedCategoryB A).ι ≅
      (DerivedCategoryB.derivedCategoryB
          (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
        (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos.mapDerivedCategory :=
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
    (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
    (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
  letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
  letI := Functor.additive_of_preserves_binary_products
    (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
    (S.coarseningHom h).toRingedToposSiteHom
  eqToIso (derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan) ≪≫
    Functor.isoWhiskerLeft _ (Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso
      (S.coarseningHom h).toRingedToposSiteHom)

include hB hvan in
/-- **Stacks 07A8, second conclusion.**  Under the hypotheses of
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`, that equivalence
`D_A(𝒪_τ) ≌ D_{A'}(𝒪_τ')`, where `A' = ε_*A`, is an equivalence of triangulated categories, and it
is given by `ε^*` and `Rε_*`:

* it is a triangulated equivalence, for the shift structure of `Lε^*` on its quasi-inverse and the
  compatible one on its functor;
* its functor, read in `D(𝒪_τ')`, is the derived pushforward `Rε_*`;
* its quasi-inverse, read in `D(𝒪_τ)`, is the derived pullback `Lε^*`, compatibly with the shift;
* since `ε^*` is exact, that quasi-inverse is `ε^*` applied termwise to complexes.

That `A'` is a weak Serre subcategory of `Mod(𝒪_τ')`, which is what makes `D_{A'}(𝒪_τ')` a
triangulated subcategory of `D(𝒪_τ')`, is the first conclusion,
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE_of_univLE`. -/
@[stacks 07A8 "second conclusion: the equivalence of triangulated categories
`D_A(𝒪_τ) ≌ D_{A'}(𝒪_τ')` given by `ε^*` and `Rε_*`"]
theorem derivedEquivalenceImageOfLE_spec :
    haveI : (DerivedCategoryB.derivedCategoryB
        (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_imageOfLE_of_univLE h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A (WeakSerre.isWeakSerre_of_isWeakSerreClass A)
        B hB hvan)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteLimits
      (S.coarseningHom h).isMorphismOfSites_toRingedToposSiteHom
      (S.isFlatMapULift_fSharp_auxHomH_coarseningHom h)
    letI := (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos_preservesFiniteColimits
    letI := Functor.additive_of_preserves_binary_products
      (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact
      (S.coarseningHom h).toRingedToposSiteHom
    letI := derivedPullbackRestrictionCommShift S h A B hB hvan
    letI := derivedEquivalenceImageOfLEInverseCommShift S h A B hB hvan
    letI := (derivedEquivalenceImageOfLE S h A B hB hvan).commShiftFunctor ℤ
    haveI := (derivedEquivalenceImageOfLE S h A B hB hvan).commShift_of_inverse ℤ
    (derivedEquivalenceImageOfLE S h A B hB hvan).IsTriangulated ∧
      (derivedEquivalenceImageOfLE S h A B hB hvan).functor ⋙
          (DerivedCategoryB.derivedCategoryB
            (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι =
        (DerivedCategoryB.derivedCategoryB A).ι ⋙
          derivedPushforward.{u} (S.coarseningHom h).toRingedToposSiteHom ∧
      ∃ e : (derivedEquivalenceImageOfLE S h A B hB hvan).inverse ⋙
          (DerivedCategoryB.derivedCategoryB A).ι =
        (DerivedCategoryB.derivedCategoryB
            (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
          derivedPullback.{u} (S.coarseningHom h).toRingedToposSiteHom,
        NatTrans.CommShift (eqToIso e).hom ℤ ∧
      Nonempty ((derivedEquivalenceImageOfLE S h A B hB hvan).inverse ⋙
          (DerivedCategoryB.derivedCategoryB A).ι ≅
        (DerivedCategoryB.derivedCategoryB
            (imageOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A)).ι ⋙
          (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos.mapDerivedCategory) :=
  ⟨(derivedEquivalenceImageOfLE_isTriangulated S h A B hB hvan).1,
    derivedEquivalenceImageOfLE_functor_comp_ι S h A B hB hvan,
    derivedEquivalenceImageOfLE_inverse_comp_ι S h A B hB hvan,
    (derivedEquivalenceImageOfLE_isTriangulated S h A B hB hvan).2,
    ⟨derivedEquivalenceImageOfLEInverseCompιIso S h A B hB hvan⟩⟩

end Derived

end Stacks.Cohomology.CompareTopologies

end
