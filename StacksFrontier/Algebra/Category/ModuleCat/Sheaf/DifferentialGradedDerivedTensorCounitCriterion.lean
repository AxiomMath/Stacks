module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorKFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionUnitQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoEquivalence

/-!
# When the derived tensor product with a bimodule is the ordinary one at a module

Let `(𝒞, 𝒪)` be a ringed site, let `𝒜'` and `𝒜''` be sheaves of differential graded
`𝒪`-algebras and let `𝒩'` be a differential graded `(𝒜', 𝒜'')`-bimodule. Choose a
quasi-isomorphism `𝒬 → 𝒩'` of left differential graded `𝒜'`-modules with `𝒬` K-flat
(Tag 0FSH, over the opposite algebra) and let `ℒ` be its cone, an acyclic left differential
graded `𝒜'`-module. For a right differential graded `𝒜'`-module `𝒴` the canonical map

`𝒴 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒴 ⊗_{𝒜'} 𝒩'`

is an isomorphism of `D(𝒜'', d)` if and only if the complex `𝒴 ⊗_{𝒜'} ℒ` is acyclic: read
through the resolution `𝒬 → 𝒩'`, the canonical map is `𝒴 ⊗ 𝒬 → 𝒴 ⊗ 𝒩'`, whose cone is
`𝒴 ⊗ ℒ`.

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_cone_iff`: for an acyclic right
  module `𝒦`, the complex `𝒦 ⊗_{𝒜'} ℒ` is acyclic if and only if `𝒦 ⊗_{𝒜'} 𝒩'` is.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductCounit_app_iff`: the
  criterion above.

## Implementation notes

The relative tensor product commutes with cones in its first variable only
(`SheafOfModules.TensorFunctorData.coneComplexIso`), so the cone in the second variable is moved
to the first by interchanging the two factors over the opposite algebra
(`SheafOfModules.RelativeTensor.dgTensorOpIso`), a left module being a bimodule over
`(𝒜'^{opp}, (𝒪, 0))` (`SheafOfModules.LeftDifferentialGradedModule.unitBimodule`). No
naturality of the interchange is needed: only the acyclicity of the two complexes is compared.
The resolution of `𝒩'` is taken over `𝒜'^{opp}`, so `ℒ` is the left module underlying the cone
of a homomorphism of right differential graded `𝒜'^{opp}`-modules.

The converse direction uses that the localization functor to `D(𝒜'', d)` inverts only
quasi-isomorphisms (`isIso_toDerivedCategory_map_iff`).

## References

* [Stacks Project, Tag 0FTL](https://stacks.math.columbia.edu/tag/0FTL)
* [Stacks Project, Tag 0FTK](https://stacks.math.columbia.edu/tag/0FTK)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Acyclic

variable {C : Type*} [Category* C] [Abelian C]

/-- A quasi-isomorphism out of an acyclic complex has an acyclic target, and conversely. -/
theorem quasiIso_iff_acyclic_of_acyclic {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) : QuasiIso f ↔ L.Acyclic := by
  rw [quasiIso_iff]
  exact forall_congr' fun i => quasiIsoAt_iff_exactAt f i (hK i)

/-- Acyclicity is invariant under isomorphism of complexes. -/
theorem acyclic_iff_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) : K.Acyclic ↔ L.Acyclic :=
  ⟨fun h i => (h i).of_iso e, fun h i => (h i).of_iso e.symm⟩

end Acyclic

section Cone

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A' A'' : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  (N' : DifferentialGradedBimodule.{u, u, u} A' A'')
  {R' : DifferentialGradedModule.{u, u, u} A'.op}
  (r' : R' ⟶ N'.toLeftDifferentialGradedModule.opRight)

/-- For an acyclic right differential graded `𝒜'`-module `𝒦` and a K-flat resolution
`r' : ℛ' → 𝒩'` over the opposite algebra, `𝒦 ⊗_{𝒜'} cone(r')` is acyclic if and only if
`𝒦 ⊗_{𝒜'} 𝒩'` is. -/
theorem acyclic_dgTensor_cone_iff (hR' : RelativeTensor.IsKFlat R')
    {K : DifferentialGradedModule.{u, u, u} A'} (hK : K.complex.Acyclic) :
    (RelativeTensor.dgTensor K (cone r').unopLeft).Acyclic ↔
      (RelativeTensor.dgTensor K N'.toLeftDifferentialGradedModule).Acyclic := by
  let DK := RelativeTensor.tensorFunctorDataDgTensorRight K.opLeft.unitBimodule
  have e₁ := (RelativeTensor.dgTensorOpIso K (cone r')).symm ≪≫ (DK.coneComplexIso r').symm
  have hsrc : (DK.functor.obj R').complex.Acyclic := hR' K.opLeft hK
  rw [acyclic_iff_of_iso e₁, acyclic_cone_iff_quasiIso, quasiIso_iff_acyclic_of_acyclic _ hsrc]
  exact acyclic_iff_of_iso <|
    RelativeTensor.dgTensorOpIso K N'.toLeftDifferentialGradedModule.opRight ≪≫
      eqToIso (by rw [LeftDifferentialGradedModule.opRight_unopLeft])

/-- For a homomorphism `p : 𝒫 → 𝒴` out of a K-flat module and an acyclic left module `ℒ`,
`cone(p) ⊗ ℒ` is acyclic if and only if `𝒴 ⊗ ℒ` is: the former is the cone of
`𝒫 ⊗ ℒ → 𝒴 ⊗ ℒ`, whose source is acyclic. -/
theorem acyclic_dgTensor_cone_iff_of_isKFlat (L : LeftDifferentialGradedModule.{u, u, u} A')
    (hL : L.complex.Acyclic) {P Y : DifferentialGradedModule.{u, u, u} A'} (p : P ⟶ Y)
    (hP : RelativeTensor.IsKFlat P) :
    (RelativeTensor.dgTensor (cone p) L).Acyclic ↔ (RelativeTensor.dgTensor Y L).Acyclic := by
  let DL := RelativeTensor.tensorFunctorDataDgTensorRight L.unitBimodule
  have hsrc : (DL.functor.obj P).complex.Acyclic := hP _ hL
  refine (acyclic_iff_of_iso (DL.coneComplexIso p).symm).trans ?_
  rw [acyclic_cone_iff_quasiIso, quasiIso_iff_acyclic_of_acyclic _ hsrc]
  rfl

end Cone

section Criterion

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A' A'' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N' : DifferentialGradedBimodule.{u, u, u} A' A'')
  {R' : DifferentialGradedModule.{u, u, u}
    (A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)).op}
  (r' : R' ⟶ N'.toLeftDifferentialGradedModule.opRight)

/-- **The derived tensor product with `𝒩'` is the ordinary one at `𝒴` exactly when `𝒴`
tensored with the cone of a K-flat resolution of `𝒩'` is acyclic.** Let `r' : ℛ' → 𝒩'` be a
quasi-isomorphism of right differential graded `𝒜'^{opp}`-modules with `ℛ'` K-flat, that is a
K-flat resolution of `𝒩'` as a left differential graded `𝒜'`-module. Then for every right
differential graded `𝒜'`-module `𝒴` the canonical map `𝒴 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒴 ⊗_{𝒜'} 𝒩'` is an
isomorphism if and only if `𝒴 ⊗_{𝒜'} cone(r')` is acyclic. -/
theorem isIso_derivedTensorProductCounit_app_iff (hR' : RelativeTensor.IsKFlat.{u, u, u, u} R')
    (hr' : (cone r').complex.Acyclic) (Y : DifferentialGradedModule.{u, u, u} A') :
    IsIso ((derivedTensorProductCounit N').app ((HomotopyCategory.quotient A').obj Y)) ↔
      (RelativeTensor.dgTensor Y (cone r').unopLeft).Acyclic := by
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let :=
    HasDerivedCategory.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  obtain ⟨P, p, hP, hp⟩ := (tensorGood (A := A')).exists_isGood Y
  have := isIso_derivedTensorProductCounit_app N' hP
  have : IsIso ((toDerivedCategory A').map ((HomotopyCategory.quotient A').map p)) :=
    isIso_toDerivedCategory_map_of_acyclic_cone A' p ((acyclic_cone_iff_quasiIso A' p).2 hp)
  have : IsIso ((toDerivedCategory A' ⋙ derivedTensorProduct N').map
      ((HomotopyCategory.quotient A').map p)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have step₁ : IsIso ((derivedTensorProductCounit N').app
        ((HomotopyCategory.quotient A').obj Y)) ↔
      IsIso ((toDerivedCategory A'').map ((HomotopyCategory.quotient A'').map
        ((tensorData N').functor.map p))) := by
    rw [← isIso_comp_left_iff ((toDerivedCategory A' ⋙ derivedTensorProduct N').map
        ((HomotopyCategory.quotient A').map p)) ((derivedTensorProductCounit N').app _),
      (derivedTensorProductCounit N').naturality, isIso_comp_left_iff]
    change IsIso ((toDerivedCategory A'').map ((HomotopyCategory.quotient A'').map
        ((pullbackTensorFunctor (idPullbackData.{u, u, u} (A := A')) (tensorData N')).map p))) ↔ _
    rw [pullbackTensorFunctor, Functor.comp_map, PullbackData.functor_map, idPullbackData_map]
    exact Iff.rfl
  rw [step₁, isIso_toDerivedCategory_map_iff A'', quasiIsomorphisms_quotient_map_iff,
    ← acyclic_cone_iff_quasiIso, acyclic_iff_of_iso ((tensorData N').coneComplexIso p)]
  refine Iff.trans (acyclic_dgTensor_cone_iff (C := X.C) N' r' hR'
    ((acyclic_cone_iff_quasiIso A' p).2 hp)).symm ?_
  exact acyclic_dgTensor_cone_iff_of_isKFlat (C := X.C) _ hr' p
    (by simp only [tensorGood] at hP; exact hP.2)

end Criterion

end DifferentialGradedModule

end SheafOfModules

end
