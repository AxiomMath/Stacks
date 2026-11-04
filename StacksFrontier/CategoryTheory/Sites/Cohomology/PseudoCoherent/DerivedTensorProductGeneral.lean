module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactnessGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSizeTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASliceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ShiftAndVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestrictionFreeModuleUniverse
public import StacksFrontier.Homology.KFlat.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of the derived tensor product above the module universe

Let `(C, O)` be a ringed site whose objects form a type one universe above its morphisms and
the sections of its structure sheaf, and let `K`, `L` be objects of `D(O)`. If `K` is
`n`-pseudo-coherent with `H^i(K) = 0` for `i > a` and `L` is `m`-pseudo-coherent with
`H^j(L) = 0` for `j > b`, then `K ⊗^{𝐋}_O L` is `t`-pseudo-coherent for
`t = max (m + a) (n + b)`; and if `K` and `L` are pseudo-coherent then so is `K ⊗^{𝐋}_O L`.

That is Stacks 09J9 at the universes of the small étale site of an algebraic space, whose
objects live in `Type (u + 1)` while its morphisms and the sections of its structure sheaf live
in `Type u`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_general`: right t-exactness of a
  derived tensor product at these universes.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherentFrom_tensor_general`: the
  quantitative statement, Stacks 09J9 part (1), at these universes.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherent_tensor_general`: preservation of
  pseudo-coherence, Stacks 09J9 part (2), at these universes.

## Implementation notes

The argument is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/DerivedTensorProduct.lean`, which
states the same two results for a `RingedSite.{0, 0, 0}` and whose implementation notes assert
that those universes are forced. They are not. Each of the three restrictions named there has
since been lifted elsewhere in the library, and this file is that argument run on the lifted
ingredients:

* the passage from a derived strictly perfect approximation on a slice to the chain-level
  approximations the definition of pseudo-coherence asks for is
  `AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived_general`, at three
  free universes;
* strict perfection of a restriction along an arrow of the site is
  `Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`, likewise;
* right t-exactness of the derived tensor product, `isLE_tensor_general` (now the base's, in
  `DerivedTensor/RightTExactnessGeneral.lean`), comes from
  the flat cover of Stacks 03EW (3) in the form
  `Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize`, whose module universe is that
  of the structure rings and whose two site universes are free, together with the ladder of
  Stacks 05T7 and Stacks 06YQ, both of which are already general. That is the only ingredient
  of the chain which the library did not have at these universes in some form.

The derived tensor products on the slices of the site are taken as a family of parameters
rather than built, since the conclusion is a property of the given `T` and does not depend on
them; a consumer hands over the canonical ones of Stacks 06YU.

Nothing here carries a Stacks registration. Tag 09J9 is already registered, on
`Stacks.SheafOfModules.DerivedTensorProduct.isPseudoCoherentFrom_derivedTensorProduct` and
`isPseudoCoherent_derivedTensorProduct`, and that registration stands; this file only widens
the universes those two are available at, which is what a consumer on the small étale site of
an algebraic space needs. The consumer this was written for is the second assertion of Stacks
0DKS — that `K ⊗^{𝐋}_{𝒪_X} M` is `Y`-perfect when `K` is perfect and `M` is `Y`-perfect — and
it supplies the pseudo-coherence clause of that assertion. The Tor clause and the
registration of 0DKS are in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectDerivedTensor`.

Both factors are replaced by representatives with flat terms: by one with no terms above the
factor's own cohomological bound for part (1), and by the colimit presentation of the
resolution of Stacks 06YS for part (2), where no bound is available. Either way the restriction
of the representative to every slice is a bounded above complex of flat modules there, or a
sequential colimit of such, hence K-flat by Stacks 06YQ; that is what the comparison of
Stacks 06YU needs on the slice.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 09J8](https://stacks.math.columbia.edu/tag/09J8)
* [Stacks Project, Tag 09J9](https://stacks.math.columbia.edu/tag/09J9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u d

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : AlgebraicGeometry.RingedSite.{u + 1, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-! ### Flat and K-flat representatives bounded above -/

omit [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive] in
/-- **Stacks 05T7 at these universes.** An object of `D^{≤ a}(O)` is represented by a complex
with flat terms and no terms above `a`: the ladder of Stacks 05T7 applied to the flat cover of
Stacks 03EW (3), whose module universe is that of the structure rings. -/
theorem exists_flatRepresentative_isStrictlyLE_general
    (K : RingedSite.DerivedModules.{u + 1, u, u, d} X) (a : ℤ) [K.IsLE a] :
    ∃ F : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := X.O) (F.X i)) ∧
        F.IsStrictlyLE a ∧ Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have hPLE : P.IsLE a :=
    (DerivedCategory.isLE_Q_obj_iff P a).1
      (DerivedCategory.TStructure.t.isLE_of_iso eP.symm a)
  let Pr : ObjectProperty (RingedSite.Modules.{u + 1, u, u} X) := fun M =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := X.O) M
  let _ : Pr.ContainsZero :=
    Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize X.O
  obtain ⟨F, f, hf, hFflat, hFLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pr
      (fun M => by
        obtain ⟨N, p, hflat, hepi⟩ :=
          Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize X.O M
        exact ⟨N, hflat, p, hepi⟩) a).2 P
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨F, hFflat, hFLE, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eP⟩⟩

/-- Every object of `D^{≤ a}(O)` is represented by a K-flat complex with no terms above `a`:
the representative with flat terms above is K-flat by Stacks 06YQ. -/
theorem exists_kFlat_isStrictlyLE_representative_general
    (K : RingedSite.DerivedModules.{u + 1, u, u, d} X) (a : ℤ) [K.IsLE a] :
    ∃ F : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ,
      Stacks.SheafOfModules.IsKFlat X.O F ∧ F.IsStrictlyLE a ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  obtain ⟨F, hFflat, hFLE, he⟩ := exists_flatRepresentative_isStrictlyLE_general X K a
  exact ⟨F, Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O F ⟨a, hFLE⟩ hFflat, hFLE, he⟩

/-- **The derived-categorical heart of Stacks 09J9 part (1).** Let `α : 𝒫 ⟶ 𝒜` and
`β : 𝒬 ⟶ ℬ` be morphisms of `D(O)` with `𝒜 ∈ D^{≤ a}` and `ℬ ∈ D^{≤ b}`, with `α` an
approximation in degree `n ≤ a` and `β` one in degree `m`. Then `𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒜 ⊗^{𝐋} ℬ` is an
approximation in degree `t = max (m + a) (n + b)`.

The morphism is factored as `𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒫 ⊗^{𝐋} ℬ ⟶ 𝒜 ⊗^{𝐋} ℬ` and right t-exactness
shifts the degree of each approximation by the bound of the fixed factor. -/
private theorem exists_approximation_derivedTensor_general
    (T : DerivedTensorProduct.{u + 1, u, u, d} X)
    (P Q A B : RingedSite.DerivedModules.{u + 1, u, u, d} X)
    (n m a b : ℤ) (hna : n ≤ a) (hA : A.IsLE a) (hB : B.IsLE b)
    (α : P ⟶ A)
    (hαiso : ∀ j : ℤ, n < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor _ n).map α))
    (β : Q ⟶ B)
    (hβiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β))
    (hβepi : Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    ∃ γ : (T.tensor.obj P).obj Q ⟶ (T.tensor.obj A).obj B,
      (∀ j : ℤ, max (m + a) (n + b) < j →
          IsIso ((DerivedCategory.homologyFunctor _ j).map γ)) ∧
        Epi ((DerivedCategory.homologyFunctor _ (max (m + a) (n + b))).map γ) := by
  have hA' := hA
  have hB' := hB
  have hP : P.IsLE a := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    have := hαiso j (by omega)
    exact (DerivedCategory.isZero_of_isLE A a j hj).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ j).map α))
  have hleg1 := DerivedCategory.approximation_of_isLE_functor (T.tensor.obj P) a
    (fun Z c hZ => by
      have := hZ
      have h := isLE_tensor_general T P Z a c
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + c) (c + a) (by omega))
    β m hβiso hβepi
  have hleg2 := DerivedCategory.approximation_of_isLE_functor (T.tensor.flip.obj B) b
    (fun Z c hZ => by
      have := hZ
      exact isLE_tensor_general T Z B c b)
    α n hαiso hαepi
  refine ⟨(T.tensor.obj P).map β ≫ (T.tensor.flip.obj B).map α, ?_, ?_⟩
  · intro j hj
    have h1 := hleg1.1 j (by omega)
    have h2 := hleg2.1 j (by omega)
    rw [Functor.map_comp]
    infer_instance
  · have h1 := DerivedCategory.epi_homologyMap_of_le _ (m + a) (max (m + a) (n + b))
      (le_max_left _ _) hleg1.1 hleg1.2
    have h2 := DerivedCategory.epi_homologyMap_of_le _ (n + b) (max (m + a) (n + b))
      (le_max_right _ _) hleg2.1 hleg2.2
    rw [Functor.map_comp]
    infer_instance

/-! ### Local approximations on the slices -/

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [hSliceDerived : ∀ U : X.C,
  HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- The tensor bifunctor of a slice is additive, at the spelling in which the restriction of
the total tensor complex is stated. -/
local instance pcgSliceTensorAdditive' (U : X.C) :
    (sheafTensor.{u + 1, u, u, u, u} (X.O.over U)).Additive :=
  sliceTensorAdditive U

/-- The tensor bifunctor of a slice is additive in its second variable, at that spelling. -/
local instance pcgSliceTensorObjAdditive' (U : X.C)
    (M : _root_.SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))) :
    ((sheafTensor.{u + 1, u, u, u, u} (X.O.over U)).obj M).Additive :=
  sliceTensorObjAdditive U M

/-- Total complexes of the tensor bifunctor of a slice exist, at that spelling. -/
local instance pcgSliceHasMapBifunctor' (U : X.C)
    (K L : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ) :=
  sliceHasMapBifunctor U K L

/-- Restriction from `O|_U`-modules to `O|_V`-modules along `g : V ⟶ U` preserves finite
limits. -/
local instance pcgOverMapLimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (_root_.SheafOfModules.overMap.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := Tensor.ringSheaf.{u + 1, u, u} X.O) g

/-- Restriction from `O|_U`-modules to `O|_V`-modules along `g : V ⟶ U` preserves finite
colimits. -/
local instance pcgOverMapColimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (_root_.SheafOfModules.overMap.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := Tensor.ringSheaf.{u + 1, u, u} X.O) g

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)] hSliceDerived
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A strictly perfect complex of `O|_V`-modules is K-flat: it has only finitely many nonzero
terms and its terms are direct summands of finite free modules, hence flat, so both clauses of
Stacks 06YQ hold on the slice. -/
private theorem kFlat_of_isStrictlyPerfect_general (V : X.C)
    (P : CochainComplex
      (_root_.SheafOfModules.{u} ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V) P) :
    Stacks.SheafOfModules.IsKFlat (X.over V).O P := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun i hi => ?_
    by_contra h
    exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)
  exact Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (X.over V).O P ⟨r, hLE⟩
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general
      (Y := X.over V) hP i

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)] hSliceDerived
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A strictly perfect complex of `O|_V`-modules has no terms above some degree. -/
private theorem exists_isZero_X_of_lt_general (V : X.C)
    (P : CochainComplex
      (_root_.SheafOfModules.{u} ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V) P) :
    ∃ r : ℤ, ∀ i : ℤ, r < i → IsZero (P.X i) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  refine ⟨r, fun i hi => ?_⟩
  by_contra h
  exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)] hSliceDerived
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive] in
/-- **The restriction of a bounded above complex of flat `O`-modules to a slice is K-flat.**
Restriction preserves the bound, being additive, and the flatness of the terms by Stacks 0E8J,
so Stacks 06YQ applies on the slice. -/
private theorem kFlat_restrictComplex_of_isStrictlyLE_general (V : X.C)
    (A : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (a : ℤ) [A.IsStrictlyLE a]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := X.O) (A.X i)) :
    Stacks.SheafOfModules.IsKFlat (X.over V).O (X.restrictComplex A V) := by
  refine Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (X.over V).O
    (X.restrictComplex A V) ⟨a, (CochainComplex.isStrictlyLE_iff _ a).2 fun i hi =>
      (_root_.SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) V).map_isZero
        (A.isZero_of_isStrictlyLE a i hi)⟩ fun i =>
    Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over.{u, u, u, u + 1}
      X V (A.X i) (hflat i)

/-- The local datum carried by an object `V` of the site: a strictly perfect complex of
`O|_V`-modules which approximates `K|_V` in degrees `> t` in the derived category of the
slice. -/
private def HasApproxG (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (t : ℤ)
    (V : X.C) : Prop :=
  ∃ P : CochainComplex
      (_root_.SheafOfModules.{u} ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V)) ℤ,
    IsStrictlyPerfect ((Tensor.ringSheaf.{u + 1, u, u} X.O).over V) P ∧
    ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K V),
      (∀ j : ℤ, t < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        Epi ((DerivedCategory.homologyFunctor _ t).map β)

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A derived strictly perfect approximation descends along an arrow of the site.**
Restriction to a smaller slice is exact, so it preserves strict perfectness and both
cohomological conditions, and it carries a complex representative of a restriction to a
complex representative of the smaller restriction. -/
private theorem hasApproxG_of_arrow
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (t : ℤ) {V W : X.C}
    (g : W ⟶ V) (h : HasApproxG X K t V) : HasApproxG X K t W := by
  obtain ⟨P, hP, β, hiso, hepi⟩ := h
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := Tensor.ringSheaf.{u + 1, u, u} X.O) g
  set F := (_root_.SheafOfModules.overMap.{u}
    (Tensor.ringSheaf.{u + 1, u, u} X.O) g).mapDerivedCategory with hF
  have hFiso := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE F
    (fun Z n hZ => have := hZ
      Stacks.Homology.isLE_mapDerivedCategory_obj
        (_root_.SheafOfModules.overMap.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) g) Z n)
    β t hiso hepi
  refine ⟨(AlgebraicGeometry.RingedSite.restrictCochainAlong X g).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Tensor.ringSheaf.{u + 1, u, u} X.O) g hP,
    ((_root_.SheafOfModules.overMap.{u}
      (Tensor.ringSheaf.{u + 1, u, u} X.O) g).mapDerivedCategoryFactors.app P).inv ≫
      F.map β ≫ (RingedSite.restrictComplexOverMapIso X K g).hom, ?_, ?_⟩
  · intro j hj
    have := hFiso.1 j hj
    have h₁ := ((_root_.SheafOfModules.overMap.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) g
      ).mapDerivedCategoryFactors.app P).isIso_inv
    have h₂ := (RingedSite.restrictComplexOverMapIso X K g).isIso_hom
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · have := hFiso.2
    have h₂ := (RingedSite.restrictComplexOverMapIso X K g).isIso_hom
    rw [Functor.map_comp, Functor.map_comp]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' hFiso.2 (IsIso.epi_of_iso _))

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A pseudo-coherent complex has, over the members of a covering of any object, a derived
strictly perfect approximation in the given degree. -/
private theorem hasApproxG_of_isPseudoCoherentComplexFrom
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (t : ℤ)
    (hK : X.IsPseudoCoherentComplexFrom K t) (U : X.C) :
    ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), Sieve.generate S g → HasApproxG X K t V := by
  obtain ⟨S, hS, hd⟩ := hK U
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨V₀, u, f, hf, -⟩ := hg
  obtain ⟨P, hP, α, hiso, hepi⟩ := hd f hf
  obtain ⟨h₁, h₂⟩ :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_Q_map α t hiso hepi
  exact hasApproxG_of_arrow X K t u ⟨P, hP, DerivedCategory.Q.map α, h₁, h₂⟩

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A derived approximation in degree `t` is in particular one in any degree `q ≥ t`. -/
private theorem HasApproxG.mono
    {K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ} {t q : ℤ} {V : X.C}
    (h : HasApproxG X K t V) (htq : t ≤ q) : HasApproxG X K q V := by
  obtain ⟨P, hP, β, hiso, hepi⟩ := h
  exact ⟨P, hP, β, fun j hj => hiso j (by omega),
    DerivedCategory.epi_homologyMap_of_le β t q htq hiso hepi⟩

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A bound on the cohomology of the restriction of a complex to a slice descends along an
arrow of the site, restriction between slices being exact. -/
private theorem isLE_restrictComplex_of_hom_general
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) {V W : X.C} (g : W ⟶ V)
    (a : ℤ) (h : (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE a) :
    (DerivedCategory.Q.obj (X.restrictComplex K W)).IsLE a := by
  have := h
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (_root_.SheafOfModules.overMap.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) g)
    (DerivedCategory.Q.obj (X.restrictComplex K V)) a
  exact DerivedCategory.TStructure.t.isLE_of_iso (RingedSite.restrictComplexOverMapIso X K g) a

omit [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive] in
/-- A bound on the cohomology of a complex of `O`-modules bounds that of its restriction to any
slice, restriction being exact. -/
private theorem isLE_restrictComplex_general
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (V : X.C) (a : ℤ)
    (h : (DerivedCategory.Q.obj K).IsLE a) :
    (DerivedCategory.Q.obj (X.restrictComplex K V)).IsLE a := by
  have := h
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (_root_.SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u + 1, u, u} X.O) V)
    (DerivedCategory.Q.obj K) a
  have e : (_root_.SheafOfModules.overFunctor.{u}
        (Tensor.ringSheaf.{u + 1, u, u} X.O) V).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (X.restrictComplex K V) :=
    (_root_.SheafOfModules.overFunctor.{u}
      (Tensor.ringSheaf.{u + 1, u, u} X.O) V).mapDerivedCategoryFactors.app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e a

/-- If every member of a covering sieve is covered by sieves whose members satisfy `Pr`, then
`Pr` holds on the members of a covering sieve. -/
private theorem exists_sieve_of_locally {C : Type*} [Category C] (J : GrothendieckTopology C)
    {U : C} (Pr : C → Prop) {S₀ : Sieve U} (hS₀ : S₀ ∈ J U)
    (key : ∀ ⦃V : C⦄ (g : V ⟶ U), S₀ g →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), T b → Pr W) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃W : C⦄ (g : W ⟶ U), S g → Pr W := by
  classical
  set T : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄, S₀ g → Sieve V := fun _ g hg => (key g hg).choose with hT
  have hTmem : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄ (hg : S₀ g), T hg ∈ J V :=
    fun _ g hg => (key g hg).choose_spec.1
  have hS₀' : Sieve.generate S₀.arrows ∈ J U := by rw [Sieve.generate_sieve]; exact hS₀
  have hbind : Sieve.bind S₀.arrows T ∈ J U := by
    refine J.transitive hS₀' _ ?_
    rintro Z b ⟨V, g, g', hg', rfl⟩
    refine J.superset_covering ?_ (J.pullback_stable g (hTmem (V := V) (g := g') hg'))
    rw [Sieve.pullback_comp]
    exact Sieve.pullback_monotone g (Sieve.le_pullback_bind S₀.arrows T g' hg')
  refine ⟨Sieve.bind S₀.arrows T, hbind, fun W b hb => ?_⟩
  obtain ⟨V, g, g', hg', hg, rfl⟩ := hb
  exact (key g' hg').choose_spec.2 g hg

omit [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (sheafTensor.{u + 1, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C, (sheafTensor.{u + 1, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M, ((sheafTensor.{u + 1, u, u, u, u} (X.over U).O).obj M).Additive] in
/-- **Derived strictly perfect approximations on a covering of every object make an object of
`D(O)` `t`-pseudo-coherent.** The covering of an object `U` that the definition of
`t`-pseudo-coherence asks for is obtained by binding the given covering of `U` with the
coverings that
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived_general` produces
over its members, which is covering by transitivity. -/
private theorem isPseudoCoherentFrom_of_locally_hasApproxG
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} X) (t : ℤ)
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ U : X.C, ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasApproxG X K t V) :
    X.IsPseudoCoherentFrom E t := by
  refine ⟨K, fun U => ?_, ⟨e⟩⟩
  obtain ⟨S₀, hS₀, hdata⟩ := h U
  have key : ∀ ⦃V : X.C⦄ (g : V ⟶ U), S₀ g →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (b : W ⟶ V), T b →
          ∃ P' : CochainComplex
              (_root_.SheafOfModules.{u} ((Tensor.ringSheaf.{u + 1, u, u} X.O).over W)) ℤ,
            IsStrictlyPerfect ((Tensor.ringSheaf.{u + 1, u, u} X.O).over W) P' ∧
            ∃ α' : P' ⟶ X.restrictComplex K W,
              (∀ j : ℤ, t < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
              Epi (HomologicalComplex.homologyMap α' t) := by
    intro V g hg
    obtain ⟨P, hP, β, hiso, hepi⟩ := hdata g hg
    exact X.exists_coveringSieve_approximation_of_derived_general V K t P hP β hiso hepi
  obtain ⟨S, hS, hP⟩ := exists_sieve_of_locally X.J _ hS₀ key
  exact ⟨S.arrows, by rwa [Sieve.generate_sieve], hP⟩

/-! ### The local step and Stacks 09J9 -/


omit hSliceDerived in
/-- **Every object of `D(O)` is represented by a complex which is K-flat and whose restriction
to every slice of the site is K-flat.** This is the resolution of Stacks 06YS in its colimit
presentation: a sequential colimit of bounded above complexes of flat `O`-modules is K-flat by
Stacks 06YQ, and so is its restriction to any slice, each stage restricting to a bounded above
complex of flat modules there. -/
theorem exists_sliceKFlat_representative_general
    (K : RingedSite.DerivedModules.{u + 1, u, u, d} X) :
    ∃ A : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ,
      Stacks.SheafOfModules.IsKFlat X.O A ∧
      (∀ W : X.C, Stacks.SheafOfModules.IsKFlat (X.over W).O (X.restrictComplex A W)) ∧
      Nonempty (DerivedCategory.Q.obj A ≅ K) := by
  obtain ⟨Kc, ⟨eKc⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨D, f, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize X.O Kc
  have hq : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hqis
  refine ⟨colimit D,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize X.O D
      hLE hflat, fun W => ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eKc⟩⟩
  have h₀ : PreservesColimitsOfSize.{u, u}
      (_root_.SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
    Stacks.SheafOfModules.pushforward_preservesColimits.{u + 1, u, u, u + 1, u, u}
      (J := X.J.over W) (K := X.J)
      (Over.forget W) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))
  have h₁ : PreservesColimitsOfSize.{0, 0}
      (_root_.SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) :=
    preservesColimitsOfSize_shrink _
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (_root_.SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize (X.over W).O
  have hres := Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
    (X.over W).O
    (D ⋙ (_root_.SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun n => by
      obtain ⟨b, hb⟩ := hLE n
      refine ⟨b, (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi => ?_⟩
      have := hb
      exact (_root_.SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).map_isZero
          ((D.obj n).isZero_of_isStrictlyLE b i hi))
    (fun n i =>
      Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over.{u, u, u, u + 1}
        X W ((D.obj n).X i) (hflat n i))
  exact CochainComplex.KFlatBifunctor.KFlat.of_iso _ hres
    (preservesColimitIso ((_root_.SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapHomologicalComplex
        (ComplexShape.up ℤ)) D).symm

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)] in
/-- **The local step of Stacks 09J9 part (1), over one object of the site.** Over an object `W`
carrying a strictly perfect approximation of `𝒜|_W` in degree `n` and one of `ℬ|_W` in degree
`m`, with `𝒜|_W ∈ D^{≤ a}`, `ℬ|_W ∈ D^{≤ b}` and `n ≤ a`, the total tensor complex
`Tot(𝒜 ⊗_O ℬ)` carries the local datum of degree `t = max (m + a) (n + b)`. -/
private theorem hasApproxG_tensorComplex
    (TT : ∀ W : X.C, DerivedTensorProduct.{u + 1, u, u, d} (X.over W))
    (A B : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (W : X.C)
    (hAW : Stacks.SheafOfModules.IsKFlat (X.over W).O (X.restrictComplex A W))
    (hBW : Stacks.SheafOfModules.IsKFlat (X.over W).O (X.restrictComplex B W))
    (n m a b : ℤ) (hna : n ≤ a)
    (hA : (DerivedCategory.Q.obj (X.restrictComplex A W)).IsLE a)
    (hB : (DerivedCategory.Q.obj (X.restrictComplex B W)).IsLE b)
    (hApp : HasApproxG X A n W) (hBpp : HasApproxG X B m W) :
    HasApproxG X (((tensorComplex X.O).obj A).obj B) (max (m + a) (n + b)) W := by
  obtain ⟨P₁, hP₁, α, hαiso, hαepi⟩ := hApp
  obtain ⟨P₂, hP₂, β, hβiso, hβepi⟩ := hBpp
  obtain ⟨γ, hγiso, hγepi⟩ := exists_approximation_derivedTensor_general (X.over W) (TT W)
    (DerivedCategory.Q.obj P₁) (DerivedCategory.Q.obj P₂)
    (DerivedCategory.Q.obj (X.restrictComplex A W))
    (DerivedCategory.Q.obj (X.restrictComplex B W)) n m a b hna hA hB
    α hαiso hαepi β hβiso hβepi
  set eS := (TT W).comparison P₁ P₂ (kFlat_of_isStrictlyPerfect_general X W P₁ hP₁)
    (kFlat_of_isStrictlyPerfect_general X W P₂ hP₂)
  set eT := (TT W).comparison (X.restrictComplex A W) (X.restrictComplex B W) hAW hBW
  set eR := DerivedCategory.Q.mapIso
    (AlgebraicGeometry.RingedSite.tensorComplexOverIso.{u + 1, u, u} X W A B)
  have k1 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso
    γ eT (max (m + a) (n + b)) hγiso hγepi
  have k2 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso
    (γ ≫ eT.hom) eR.symm (max (m + a) (n + b)) k1.1 k1.2
  have k3 := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.iso_comp_approximation
    eS.symm ((γ ≫ eT.hom) ≫ eR.symm.hom) (max (m + a) (n + b)) k2.1 k2.2
  exact ⟨((tensorComplex (X.over W).O).obj P₁).obj P₂,
    Stacks.SheafOfModules.Tensor.isStrictlyPerfect_tensorComplex (X.over W).O P₁ P₂ hP₁ hP₂,
    eS.symm.hom ≫ (γ ≫ eT.hom) ≫ eR.symm.hom, k3.1, k3.2⟩

/-- **Stacks 09J9, part (1), above the module universe.** Let `(C, O)` be a ringed site whose
objects form a type one universe above its morphisms and the sections of its structure sheaf,
and let `K`, `L` be objects of `D(O)`. If `K` is `n`-pseudo-coherent with `H^i(K) = 0` for
`i > a`, and `L` is `m`-pseudo-coherent with `H^j(L) = 0` for `j > b`, then `K ⊗^{𝐋}_O L` is
`t`-pseudo-coherent for `t = max (m + a) (n + b)`.

If `a < n` then `t > a + b`, so the conclusion follows from right t-exactness alone. In the
remaining case
`n ≤ a`, and both factors are replaced by representatives with flat terms and no terms above
their own bounds, which are K-flat and restrict to K-flat complexes on every slice; on those
the derived tensor product is the total tensor complex, so that complex represents
`K ⊗^{𝐋} L`. -/
theorem isPseudoCoherentFrom_tensor_general
    (T : DerivedTensorProduct.{u + 1, u, u, d} X)
    (TT : ∀ W : X.C, DerivedTensorProduct.{u + 1, u, u, d} (X.over W))
    (K L : RingedSite.DerivedModules.{u + 1, u, u, d} X) (n m a b : ℤ)
    (hK : X.IsPseudoCoherentFrom K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{u + 1, u, u} X) i).obj K))
    (hL : X.IsPseudoCoherentFrom L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{u + 1, u, u} X) j).obj L)) :
    X.IsPseudoCoherentFrom ((T.tensor.obj K).obj L) (max (m + a) (n + b)) := by
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).2 hKa
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).2 hLb
  rcases lt_or_ge a n with hna | hna
  · have hT : ((T.tensor.obj K).obj L).IsLE (a + b) := isLE_tensor_general T K L a b
    have := le_max_right (m + a) (n + b)
    have hLE2 : ((T.tensor.obj K).obj L).IsLE (max (m + a) (n + b) - 1) := by
      have := hT
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + b)
        (max (m + a) (n + b) - 1) (by omega)
    have := hLE2
    have := X.isPseudoCoherentFrom_of_isLE ((T.tensor.obj K).obj L)
      (max (m + a) (n + b) - 1)
    simpa only [sub_add_cancel] using this
  have rep : ∀ (E : RingedSite.DerivedModules.{u + 1, u, u, d} X) (c : ℤ) [E.IsLE c],
      ∃ A : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ,
        Stacks.SheafOfModules.IsKFlat X.O A ∧
        (∀ W : X.C, Stacks.SheafOfModules.IsKFlat (X.over W).O (X.restrictComplex A W)) ∧
        (DerivedCategory.Q.obj A).IsLE c ∧ Nonempty (DerivedCategory.Q.obj A ≅ E) := by
    intro E c _
    obtain ⟨A, hflat, hLE, he⟩ := exists_flatRepresentative_isStrictlyLE_general X E c
    refine ⟨A, Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O A ⟨c, hLE⟩ hflat,
      fun W => ?_, ?_, he⟩
    · have := hLE
      exact kFlat_restrictComplex_of_isStrictlyLE_general X W A c hflat
    · rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
  obtain ⟨A, hAk, hAW, hQA, ⟨eA⟩⟩ := rep K a
  obtain ⟨B, hBk, hBW, hQB, ⟨eB⟩⟩ := rep L b
  have eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  refine isPseudoCoherentFrom_of_locally_hasApproxG X _ (max (m + a) (n + b)) _ eG fun U => ?_
  obtain ⟨S₁, hS₁, hd₁⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X A n
    (X.isPseudoCoherentComplexFrom_of_iso_general K n hK A eA) U
  obtain ⟨S₂, hS₂, hd₂⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X B m
    (X.isPseudoCoherentComplexFrom_of_iso_general L m hL B eB) U
  refine ⟨Sieve.generate S₁ ⊓ Sieve.generate S₂, X.J.intersection_covering hS₁ hS₂,
    fun V g hg => ?_⟩
  exact hasApproxG_tensorComplex X TT A B V (hAW V) (hBW V) n m a b hna
    (isLE_restrictComplex_general X A V a hQA) (isLE_restrictComplex_general X B V b hQB)
    (hd₁ g hg.1) (hd₂ g hg.2)

/-- **Stacks 09J9, part (2), above the module universe.** The derived tensor product of two
pseudo-coherent objects of `D(O)` is pseudo-coherent.

Neither factor is assumed bounded above, so the representatives are the resolutions of Stacks
06YS taken in their colimit presentation, which stay K-flat after restriction to any slice.
`Tot(𝒜 ⊗_O ℬ)` is then a representative of `K ⊗^{𝐋} L`, and it suffices to see that it is
`q`-pseudo-coherent for every `q`. The cohomological bounds that part (1) needs are produced on
the covering itself: a strictly perfect approximation in degree `0` over an object of the site
has only finitely many nonzero terms, so the two factors are bounded above there, say by `a`
and `b`, and the thresholds `n = min (q - b) a` and `m = min (q - a) b` give
`max (m + a) (n + b) ≤ q` and `n ≤ a`. -/
@[sga "6 I 2.16" "partial", sga "6 III 1.8" "Case X_i = Y_i = S"]
theorem isPseudoCoherent_tensor_general
    (T : DerivedTensorProduct.{u + 1, u, u, d} X)
    (TT : ∀ W : X.C, DerivedTensorProduct.{u + 1, u, u, d} (X.over W))
    (K L : RingedSite.DerivedModules.{u + 1, u, u, d} X)
    (hK : X.IsPseudoCoherent K) (hL : X.IsPseudoCoherent L) :
    X.IsPseudoCoherent ((T.tensor.obj K).obj L) := by
  classical
  obtain ⟨Kc, hKc, ⟨eKc⟩⟩ := hK
  obtain ⟨Lc, hLc, ⟨eLc⟩⟩ := hL
  obtain ⟨A, hAk, hAW, ⟨eA⟩⟩ := exists_sliceKFlat_representative_general X K
  obtain ⟨B, hBk, hBW, ⟨eB⟩⟩ := exists_sliceKFlat_representative_general X L
  have hApc : ∀ q : ℤ, X.IsPseudoCoherentComplexFrom A q := fun q =>
    X.isPseudoCoherentComplexFrom_of_iso_general K q ⟨Kc, hKc q, ⟨eKc⟩⟩ A eA
  have hBpc : ∀ q : ℤ, X.IsPseudoCoherentComplexFrom B q := fun q =>
    X.isPseudoCoherentComplexFrom_of_iso_general L q ⟨Lc, hLc q, ⟨eLc⟩⟩ B eB
  have eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  have hle : ∀ (E : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) {V : X.C},
      HasApproxG X E 0 V → ∃ c : ℤ, (DerivedCategory.Q.obj (X.restrictComplex E V)).IsLE c := by
    rintro E V ⟨P, hP, β, hiso, -⟩
    obtain ⟨c, hc⟩ := exists_isZero_X_of_lt_general X V P hP
    exact ⟨max 0 c, DerivedCategory.isLE_Q_obj_of_approximation 0 c hc β hiso⟩
  have key : ∀ (q : ℤ) (U : X.C), ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g →
        HasApproxG X (((tensorComplex X.O).obj A).obj B) q V := by
    intro q U
    obtain ⟨S₁, hS₁, hd₁⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X A 0 (hApc 0) U
    obtain ⟨S₂, hS₂, hd₂⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X B 0 (hBpc 0) U
    refine exists_sieve_of_locally X.J _ (X.J.intersection_covering hS₁ hS₂) fun V g hg => ?_
    obtain ⟨c, hAV⟩ := hle A (hd₁ g hg.1)
    obtain ⟨d, hBV⟩ := hle B (hd₂ g hg.2)
    obtain ⟨S₃, hS₃, hd₃⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X A (min (q - d) c)
      (hApc _) V
    obtain ⟨S₄, hS₄, hd₄⟩ := hasApproxG_of_isPseudoCoherentComplexFrom X B (min (q - c) d)
      (hBpc _) V
    refine ⟨Sieve.generate S₃ ⊓ Sieve.generate S₄, X.J.intersection_covering hS₃ hS₄,
      fun W h hh => ?_⟩
    refine HasApproxG.mono X (hasApproxG_tensorComplex X TT A B W (hAW W) (hBW W)
      (min (q - d) c) (min (q - c) d) c d (min_le_right _ _)
      (isLE_restrictComplex_of_hom_general X A h c hAV)
      (isLE_restrictComplex_of_hom_general X B h d hBV) (hd₃ h hh.1) (hd₄ h hh.2)) ?_
    have := min_le_left (q - c) d
    have := min_le_left (q - d) c
    exact max_le (by omega) (by omega)
  refine ⟨((tensorComplex X.O).obj A).obj B, fun q => ?_, ⟨eG⟩⟩
  exact X.isPseudoCoherentComplexFrom_of_iso_general _ q
    (isPseudoCoherentFrom_of_locally_hasApproxG X _ q _ eG (key q)) _ eG

end Stacks.SheafOfModules.DerivedTensorProduct

end
