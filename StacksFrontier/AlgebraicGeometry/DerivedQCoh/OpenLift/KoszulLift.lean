module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyBijective
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystemPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct

/-!
# Lifting a map out of the structure sheaf over a quasi-compact open

Let `A` be a commutative ring, `X = Spec A` and `U ⊆ X` a quasi-compact open. Writing `U` as a
finite union `D(f₁) ∪ ⋯ ∪ D(f_r)` of basic opens, the inverse system `e ↦ Iₑ` of sheafified
truncated Koszul complexes `Koszul.DerivedSystem.koszulDerivedSystem` consists of perfect objects
of `D(𝒪_X)` equipped with maps `Iₑ ⟶ 𝒪_X` which become isomorphisms after restriction to `U`. Every
map `𝒪_X|_U ⟶ E|_U` into the restriction of an object of `D_QCoh(𝒪_X)` is the restriction of a map
`Iₑ ⟶ E` for some `e`, read through the isomorphism `𝒪_X|_U ≅ Iₑ|_U`. This is the case `E = 𝒪_X` of
[Stacks, Tag 08EH].

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_unionOfBasicOpens_eq`: a quasi-compact open of `Spec A` is
  the union `Koszul.DerivedSystem.unionOfBasicOpens f` of the basic opens of a finite family.
* `Stacks.DerivedQCoh.OpenLift.exists_koszulDerivedSystem_lift`: the lifting statement for the
  union of a given finite family of basic opens.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_lift_of_structureSheaf_unionOfBasicOpens`: the
  lifting statement for the union of a given finite family of basic opens, with the perfectness
  of the source recorded.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_lift_of_structureSheaf`: the same for an
  arbitrary quasi-compact open.
* `Stacks.DerivedQCoh.OpenLift.isPerfect_derTensor_koszulDerivedSystem_obj`: the derived tensor
  product of a perfect object with a stage of the Koszul system is perfect.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Koszul.DerivedSystem Stacks.Cohomology.OpenSubspace

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Quasi-compact opens of an affine scheme -/

/-- A quasi-compact open of `Spec A` is the union `unionOfBasicOpens f` of the basic opens of a
finite family `f : Fin r → A`. -/
theorem exists_unionOfBasicOpens_eq {A : CommRingCat.{u}} (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) :
    ∃ (r : ℕ) (f : Fin r → A), unionOfBasicOpens f = U := by
  classical
  obtain ⟨s, hs, hEq⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
      (X := Spec A) (U := (U : Set (Spec A)))).mp ⟨hU, U.isOpen⟩
  let : Fintype s := hs.fintype
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g : Fin (Fintype.card s) → Γ(Spec A, ⊤) := fun i ↦ (e i).val
  let f : Fin (Fintype.card s) → A := fun i ↦ (Scheme.ΓSpecIso A).hom (g i)
  have hU' : U = ⨆ i, (Spec A).basicOpen (g i) := by
    apply SetLike.coe_injective
    rw [hEq]
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Opens.mem_iSup]
    exact ⟨fun ⟨i, hi, hx⟩ ↦ ⟨e.symm ⟨i, hi⟩, by simpa [g, e] using hx⟩,
      fun ⟨i, hx⟩ ↦ ⟨(e i).val, (e i).property, by simpa [g] using hx⟩⟩
  refine ⟨Fintype.card s, f, ?_⟩
  rw [hU']
  exact iSup_congr fun i ↦ (AlgebraicGeometry.basicOpen_eq_of_affine' (g i)).symm

/-! ### Lifting along the Koszul system -/

variable {A : CommRingCat.{u}} {r : ℕ}

/-- Let `U` be the union of the basic opens of a finite family. For `E` in `D_QCoh(𝒪_X)`, every
map `𝒪_X|_U ⟶ E|_U` out of the restriction of the structure sheaf is the restriction of a map
`Iₑ ⟶ E` out of a stage of the Koszul system, read through the restriction of `Iₑ ⟶ 𝒪_X`. -/
theorem exists_koszulDerivedSystem_lift (f : Fin r → A) (E : derivedCat A)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E)
    (α : (restrictionToUnion f).obj (structureSheafObject A) ⟶ (restrictionToUnion f).obj E) :
    ∃ (e : ℕ) (γ : (koszulDerivedSystem f).obj (op e) ⟶ E),
      (restrictionToUnion f).map (canonicalKoszulToStructureSheaf f e) ≫ α =
        (restrictionToUnion f).map γ := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{u + 1})
  obtain ⟨x, hx⟩ := (bijective_cohomologyComparison f E hE).2 (sectionsEquivOfUnion f E α)
  replace hx : cohomologyComparisonHom f E x = α := (sectionsEquivOfUnion f E).injective hx
  obtain ⟨e, γ, hγ⟩ := Concrete.colimit_exists_rep (homGroupSystem f E) x
  refine ⟨e, γ, ?_⟩
  have h : (restrictionIsoOfUnion f e).hom ≫ (restrictionToUnion f).map γ = α := by
    rw [← cohomologyComparisonHom_colimit_ι f E e γ, hγ, hx]
  rw [← restrictionIsoOfUnion_inv, ← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Let `U` be the union of the basic opens of a finite family. For `E` in `D_QCoh(𝒪_X)`, every
map `𝒪_X|_U ⟶ E|_U` is the restriction of a map `I ⟶ E` out of a perfect object `I` of `D(𝒪_X)`,
read through the restriction of a map `I ⟶ 𝒪_X` that becomes invertible on `U`. -/
theorem exists_isPerfect_lift_of_structureSheaf_unionOfBasicOpens (f : Fin r → A)
    (E : derivedCat A) (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E)
    (α : (restrictionToUnion f).obj (structureSheafObject A) ⟶ (restrictionToUnion f).obj E) :
    ∃ I : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) I ∧
      ∃ (β : I ⟶ structureSheafObject A) (γ : I ⟶ E),
        IsIso ((restrictionToUnion f).map β) ∧
        (restrictionToUnion f).map β ≫ α = (restrictionToUnion f).map γ := by
  obtain ⟨e, γ, hγ⟩ := exists_koszulDerivedSystem_lift f E hE α
  exact ⟨(koszulDerivedSystem f).obj (op e), isPerfect_koszulDerivedSystem_obj f e,
    canonicalKoszulToStructureSheaf f e, γ, isIso_restrictionToUnion_map_canonical f e, hγ⟩


/-- Let `U` be a quasi-compact open of `X = Spec A`. For `E` in `D_QCoh(𝒪_X)`, every map
`𝒪_X|_U ⟶ E|_U` extends to a perfect object of `D(𝒪_X)` mapping to `𝒪_X` by a map that becomes
invertible on `U`. -/
theorem exists_isPerfect_lift_of_structureSheaf {A : CommRingCat.{u}} (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (E : derivedCat A)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E)
    (α : (derivedRestriction (Spec A).ringCatSheaf U).obj (structureSheafObject A) ⟶
      (derivedRestriction (Spec A).ringCatSheaf U).obj E) :
    ∃ I : derivedCat A,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) I ∧
      ∃ (β : I ⟶ structureSheafObject A) (γ : I ⟶ E),
        IsIso ((derivedRestriction (Spec A).ringCatSheaf U).map β) ∧
        (derivedRestriction (Spec A).ringCatSheaf U).map β ≫ α =
          (derivedRestriction (Spec A).ringCatSheaf U).map γ := by
  obtain ⟨r, f, hf⟩ := exists_unionOfBasicOpens_eq U hU
  subst hf
  exact exists_isPerfect_lift_of_structureSheaf_unionOfBasicOpens f E hE α


/-- The derived tensor product of a perfect object with a stage of the Koszul system is
perfect. -/
theorem isPerfect_derTensor_koszulDerivedSystem_obj {A : CommRingCat.{u}} {r : ℕ}
    (f : Fin r → A) (e : ℕ) (E : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
      (((Stacks.Cohomology.TorAmplitude.derTensor (Spec A).toRingedSpace).tensor.obj E).obj
        ((koszulDerivedSystem f).obj (op e))) :=
  AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct
    (Spec A).toRingedSpace E ((koszulDerivedSystem f).obj (op e)) hE
    (isPerfect_koszulDerivedSystem_obj f e)

end Stacks.DerivedQCoh.OpenLift

end
