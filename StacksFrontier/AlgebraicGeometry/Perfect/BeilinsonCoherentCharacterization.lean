module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing bounded coherent complexes on projective space over a field

Let `k` be a field, let `n ≥ 0` and let `K` be an object of `D_QCoh(𝒪_{ℙⁿ_k})`.  [Stacks, Tag
0FYB] states that the following are equivalent:

1. `K` is an object of `D^b_{Coh}(𝒪_{ℙⁿ_k})`;
2. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, E ⊗^𝐋 K)` is finite for every perfect object `E` of `D(𝒪_{ℙⁿ_k})`;
3. `∑_{i ∈ ℤ} dim_k Ext^i_{ℙⁿ_k}(E, K)` is finite for every perfect object `E`;
4. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, K ⊗^𝐋 𝒪(d))` is finite for `d = 0, 1, …, n`.

This file states the four conditions and proves the implication (2) ⟹ (4). The equivalence of
all four, for `K` in `D_QCoh(𝒪_{ℙⁿ_k})`, is
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.tfae_isBoundedCoherent` in
`StacksFrontier/AlgebraicGeometry/Perfect/BeilinsonCoherentCharacterizationTFAE.lean`.

## Main definitions

* `HasFiniteTotalExt`: finiteness of the total dimension of `Ext^•` over the base field, for two
  objects of the derived category of modules on a scheme over `Spec k`.  Finiteness of the sum
  `∑_{i ∈ ℤ} dim_k Ext^i` is expressed without choosing bases: every `Ext^i` is a finite
  `k`-module and only finitely many of them are nonzero.
* `IsBoundedCoherent`, `HasFiniteTotalTensorCohomology`, `HasFiniteTotalPerfectExt`,
  `HasFiniteTotalTwistCohomology`: conditions (1), (2), (3) and (4) of [Stacks, Tag 0FYB].

## Main results

* `HasFiniteTotalExt.of_iso_right`, `HasFiniteTotalExt.of_iso_left`: finiteness of the total
  `Ext` depends only on the isomorphism classes of the two arguments.
* `isPerfect_singleFunctor_twistOver`: the twisting sheaf `𝒪_{ℙⁿ_S}(d)`, placed in cohomological
  degree zero, is a perfect object of `D(𝒪_{ℙⁿ_S})`, for every scheme `S` and every `d ∈ ℤ`.
* `hasFiniteTotalTwistCohomology_of_hasFiniteTotalTensorCohomology`: **[Stacks, Tag 0FYB],
  (2) ⟹ (4)**.

## Implementation notes

*Cohomology is `Ext` from the structure sheaf.*  `H^i(ℙⁿ_k, L)` is `Ext^i(𝒪_X[0], L)`, and
`𝒪_X[0]` is `Stacks.DerivedTensor.RingedSite.unitObject` at the ringed site of opens of `ℙⁿ_k`,
which is by definition the structure sheaf placed in cohomological degree zero.  The `k`-module
structure on `Ext` is `AlgebraicGeometry.modulesLinear`, the linear structure that the structure
morphism `ℙⁿ_k ⟶ Spec k` induces on the category of modules.

*The derived tensor product* is the canonical one of [Stacks, Tag 06YU],
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, read at the ringed site of
opens.  Its commutativity constraint at a pair of objects is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`, which is what turns
`𝒪(d) ⊗^𝐋 K` into `K ⊗^𝐋 𝒪(d)`; the source's condition (4) is written with the twist on the
right, and condition (2) quantifies over a perfect object on the left.

*Perfectness of the twist.*  Condition (2) is applied at `E = 𝒪(d)[0]`, so what (2) ⟹ (4)
needs of the twisting sheaf is exactly that it is perfect in degree zero.  That is assembled
here from three results: the twisting sheaf of `ℙⁿ_S` is invertible for every integer
`d` (`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver`), an invertible
module on a scheme is finite locally free
(`AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_of_isInvertible`), and a finite
locally free module placed in degree zero is a perfect object
(`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`).  The two spellings of
invertibility of a sheaf of modules in this library are identified by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`.

*Which implications are proved here.*  Only (2) ⟹ (4); the remaining implications are proved
in `StacksFrontier/AlgebraicGeometry/Perfect/BeilinsonCoherentCharacterizationTFAE.lean`, see its
module documentation for the argument.

## References

* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 0FYA](https://stacks.math.columbia.edu/tag/0FYA)
* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SpaceInverseSystems

namespace Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The standing hypotheses of the derived tensor product, at a site of opens

The tensor product of `O_X`-modules is additive in each variable and the degreewise tensor
products of two complexes of `O_X`-modules have total complexes.  These are the standing
hypotheses of the derived tensor product of [Stacks, Tag 06YU]:
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` cannot be stated without them, so they
are needed to state conditions (2) and (4) below at all.

They are theorems rather than hypotheses here.  `Stacks.SheafOfModules.Tensor.sheafTensor` is
additive in each variable over any site with the sheafification hypotheses
(`Stacks.SheafOfModules.Tensor.sheafTensor_additive` and its companions), and the site of opens
of a ringed space has them.  What is missing is only that instance search does not reach those
theorems at the spelling in which the goals arise here: the ring sheaf is
`(ringedSiteOfSpace X).O`, and `ringedSiteOfSpace` is a plain `def`, so the discrimination key
of the goal is `RingedSite.O (ringedSiteOfSpace _)` while the library instances are keyed on
`X.sheaf`; search never tries them and diverges instead.  Raising the transparency of
`ringedSiteOfSpace` does not help, since the indexing is what has to change and `[reducible]`
cannot be set locally.  So the three are pinned by hand, exactly as
`Stacks.Cohomology.RingedSpaceCompact` pins them for the parallel
`AlgebraicGeometry.RingedSpace.ringedSite`.

`(ringedSiteOfSpace X).O` is `X.sheaf` — the field is projected from a constructor application,
so the two are the same term up to iota — and these are properties of that one sheaf of rings.
Nothing is identified with anything, and no statement below carries them as a hypothesis. -/

/-- `⊗_{O_X}` is additive in its first variable. -/
local instance opensSheafTensorAdditive (X : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ringedSiteOfSpace X).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive
    (J := _root_.Opens.grothendieckTopology X.carrier) X.sheaf

/-- `M ⊗_{O_X} -` is additive. -/
local instance opensSheafTensorObjAdditive (X : RingedSpace.{u, u})
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteOfSpace X).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ringedSiteOfSpace X).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
    (J := _root_.Opens.grothendieckTopology X.carrier) X.sheaf M

/-- The total complex of the tensor double complex of two complexes of `O_X`-modules exists. -/
local instance opensHasMapBifunctorSheafTensor (X : RingedSpace.{u, u})
    (K L : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSiteOfSpace X).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (ringedSiteOfSpace X).O)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := _root_.Opens.grothendieckTopology X.carrier) X.sheaf K L

/-! ### Finite total `Ext` over the base field -/

/-- **Finiteness of `∑_{i ∈ ℤ} dim_k Ext^i(E, L)`** for two objects of the derived category of
modules on a scheme `X` over `Spec k`.

The sum is expressed without choosing bases: each `Ext^i(E, L)` is a finite `k`-module, and only
finitely many of them are nonzero.  The `k`-module structure is the one the structure morphism
`X ⟶ Spec k` induces, `AlgebraicGeometry.modulesLinear`. -/
def HasFiniteTotalExt (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (E L : DerivedCategory X.left.Modules) : Prop :=
  letI : Linear k X.left.Modules := AlgebraicGeometry.modulesLinear k X
  (∀ i : ℤ, Module.Finite k (DerivedCategory.Ext E L i)) ∧
    {i : ℤ | ¬ Subsingleton (DerivedCategory.Ext E L i)}.Finite

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}

/-- Post-composition with an isomorphism is a surjective `k`-linear map on `Ext`. -/
private theorem surjective_rightComp_ext
    {E L L' : DerivedCategory X.left.Modules} (e : L ≅ L') (i : ℤ) :
    letI : Linear k X.left.Modules := AlgebraicGeometry.modulesLinear k X
    Function.Surjective
      (Linear.rightComp k E ((shiftFunctor (DerivedCategory X.left.Modules) i).map e.hom)) :=
  fun f => ⟨f ≫ (shiftFunctor (DerivedCategory X.left.Modules) i).map e.inv, by simp⟩

/-- Pre-composition with an isomorphism is a surjective `k`-linear map on `Ext`. -/
private theorem surjective_leftComp_ext
    {E E' L : DerivedCategory X.left.Modules} (e : E ≅ E') (i : ℤ) :
    letI : Linear k X.left.Modules := AlgebraicGeometry.modulesLinear k X
    Function.Surjective
      (Linear.leftComp k ((shiftFunctor (DerivedCategory X.left.Modules) i).obj L) e.inv) :=
  fun f => ⟨e.hom ≫ f, by simp⟩

/-- **Finiteness of the total `Ext` depends only on the isomorphism class of the target.** -/
theorem HasFiniteTotalExt.of_iso_right {E L L' : DerivedCategory X.left.Modules}
    (h : HasFiniteTotalExt k X E L) (e : L ≅ L') : HasFiniteTotalExt k X E L' := by
  obtain ⟨hfin, hsupp⟩ := h
  let : Linear k X.left.Modules := AlgebraicGeometry.modulesLinear k X
  exact ⟨fun i => have := hfin i; Module.Finite.of_surjective _ (surjective_rightComp_ext e i),
    hsupp.subset fun i hi hsub => hi ((surjective_rightComp_ext (k := k) e i).subsingleton)⟩

/-- **Finiteness of the total `Ext` depends only on the isomorphism class of the source.** -/
theorem HasFiniteTotalExt.of_iso_left {E E' L : DerivedCategory X.left.Modules}
    (h : HasFiniteTotalExt k X E L) (e : E ≅ E') : HasFiniteTotalExt k X E' L := by
  obtain ⟨hfin, hsupp⟩ := h
  let : Linear k X.left.Modules := AlgebraicGeometry.modulesLinear k X
  exact ⟨fun i => have := hfin i; Module.Finite.of_surjective _ (surjective_leftComp_ext e i),
    hsupp.subset fun i hi hsub => hi ((surjective_leftComp_ext (k := k) e i).subsingleton)⟩

/-! ### Perfectness of the twisting sheaf in degree zero -/

/-- **The twisting sheaf `𝒪_{ℙⁿ_S}(d)`, placed in cohomological degree zero, is a perfect object
of `D(𝒪_{ℙⁿ_S})`**, for every scheme `S` and every `d ∈ ℤ`.

The twisting sheaf is invertible by [Stacks, Tag 01MU] in the form
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver`, an invertible module
on a scheme is finite locally free, and a finite locally free module in degree zero is perfect
by [Stacks, Tag 08CM]. -/
theorem isPerfect_singleFunctor_twistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOver n S).toRingedSpace)
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (ProjTwistTensorPow.twistOver n S d)) :=
  AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree
    (projectiveSpaceOver n S) (ProjTwistTensorPow.twistOver n S d)
    (@AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_of_isInvertible
      (projectiveSpaceOver n S) (ProjTwistTensorPow.twistOver n S d)
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        (projectiveSpaceOver n S).sheaf.obj (projectiveSpaceOver n S).ringCatSheaf.property
        (ProjTwistTensorPow.twistOver n S d)).mpr
        (ProjTwistTensorPow.isInvertibleModule_twistOver n S d)))

/-! ### The four conditions of Tag 0FYB -/

section Conditions

variable (k) (n : ℕ)

/-- `ℙⁿ_k` read as an object over `Spec k`, through its structure morphism. -/
abbrev projSpaceOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k))

/-- The ringed site of opens of `ℙⁿ_k`, the shape in which the derived tensor product of
[Stacks, Tag 06YU] and its commutativity constraint are available. -/
abbrev projSpaceSite : _root_.AlgebraicGeometry.RingedSite.{u, u, u} :=
  ringedSiteOfSpace (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace

/-- The canonical derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_{ℙⁿ_k})`. -/
abbrev projDerivedTensor :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (projSpaceSite k n).O :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (projSpaceSite k n).O

/-- **Condition (1) of [Stacks, Tag 0FYB]**: `K` is an object of `D^b_{Coh}(𝒪_{ℙⁿ_k})`, that is,
`K` is bounded and all of its cohomology sheaves are coherent. -/
def IsBoundedCoherent
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) : Prop :=
  DerivedCategoryB.derivedCategoryBBounded
    (fun M : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules => M.IsCoherent) K

/-- **Condition (2) of [Stacks, Tag 0FYB]**: `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, E ⊗^𝐋 K)` is finite for
every perfect object `E` of `D(𝒪_{ℙⁿ_k})`.  Cohomology is `Ext` from the structure sheaf placed
in degree zero. -/
def HasFiniteTotalTensorCohomology
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) : Prop :=
  ∀ E : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules,
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) E →
      HasFiniteTotalExt k (projSpaceOver k n)
        (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n))
        (((projDerivedTensor k n).tensor.obj E).obj K)

/-- **Condition (3) of [Stacks, Tag 0FYB]**: `∑_{i ∈ ℤ} dim_k Ext^i_{ℙⁿ_k}(E, K)` is finite for
every perfect object `E` of `D(𝒪_{ℙⁿ_k})`. -/
def HasFiniteTotalPerfectExt
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) : Prop :=
  ∀ E : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules,
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) E →
      HasFiniteTotalExt k (projSpaceOver k n) E K

/-- **Condition (4) of [Stacks, Tag 0FYB]**: `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, K ⊗^𝐋 𝒪(d))` is finite
for `d = 0, 1, …, n`. -/
def HasFiniteTotalTwistCohomology
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) : Prop :=
  ∀ d : ℕ, d ≤ n →
    HasFiniteTotalExt k (projSpaceOver k n)
      (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n))
      (((projDerivedTensor k n).tensor.obj K).obj
        ((DerivedCategory.singleFunctor
            (projectiveSpaceOverRing n (CommRingCat.of k)).Modules 0).obj
          (ProjTwistTensorPow.twistOver n (Spec (CommRingCat.of k)) (d : ℤ))))

end Conditions

/-! ### (2) implies (4) -/

/-- **[Stacks, Tag 0FYB], (2) ⟹ (4).**  Let `k` be a field, let `n ≥ 0` and let `K` be an object
of `D(𝒪_{ℙⁿ_k})`.  If `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, E ⊗^𝐋 K)` is finite for every perfect object
`E`, then `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, K ⊗^𝐋 𝒪(d))` is finite for `d = 0, 1, …, n`.

The source's proof is *"this is immediate, as `𝒪(d)` is a perfect object"*: apply the hypothesis
at `E = 𝒪(d)[0]`, which is perfect by
`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isPerfect_singleFunctor_twistOver`,
and move the twist past `K` with the commutativity constraint of the derived tensor product
([Stacks, Tag 0FPT]).  No condition on `d` beyond the source's `0 ≤ d ≤ n` is used, and the
conclusion holds for every `d ∈ ℤ`; it is stated for `d = 0, …, n` because that is the source's
condition (4). -/
@[stacks 0FYB "part (2) ⟹ part (4)"]
theorem hasFiniteTotalTwistCohomology_of_hasFiniteTotalTensorCohomology
    (k : Type u) [Field k] (n : ℕ)
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hK : HasFiniteTotalTensorCohomology k n K) :
    HasFiniteTotalTwistCohomology k n K := by
  intro d _
  exact (hK _ (isPerfect_singleFunctor_twistOver n (Spec (CommRingCat.of k)) (d : ℤ))).of_iso_right
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso (projSpaceSite k n)
      (projDerivedTensor k n) _ K)

end Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

end
