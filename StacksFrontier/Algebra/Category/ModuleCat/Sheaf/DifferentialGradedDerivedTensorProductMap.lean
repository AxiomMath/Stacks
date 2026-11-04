module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorBimoduleMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorCounitCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProductComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensor

/-!
# The derived tensor product along a homomorphism of bimodules

Let `(𝒞, 𝒪)` be a ringed site, let `𝒜` and `ℬ` be sheaves of differential graded `𝒪`-algebras
and let `ν : 𝒩 ⟶ 𝒩'` be a homomorphism of differential graded `(𝒜, ℬ)`-bimodules. The maps
`ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'` induce a canonical natural transformation

`t : (- ⊗^𝐋_𝒜 𝒩) ⟶ (- ⊗^𝐋_𝒜 𝒩')`

of functors `D(𝒜, d) ⥤ D(ℬ, d)`, whose value on a flat and K-flat module `𝒫` is the map
`𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'`. If `ν` is an isomorphism on cohomology sheaves, `t` is an isomorphism of
functors ([Stacks, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ)).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.tensorDataMap`: the natural transformation
  `- ⊗_𝒜 𝒩 ⟶ - ⊗_𝒜 𝒩'` of functors of differential graded modules.
* `SheafOfModules.DifferentialGradedModule.homotopyTensorMap`: the transformation it induces on
  the homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductMap`: **the canonical
  transformation `t : (- ⊗^𝐋_𝒜 𝒩) ⟶ (- ⊗^𝐋_𝒜 𝒩')`**, induced by the universal property of the
  left derived functor.

## Main results

* `SheafOfModules.RelativeTensor.quasiIso_dgTensorMapLeft`: for a K-flat right differential
  graded `𝒜`-module `𝒫` and a quasi-isomorphism `f : 𝒩 ⟶ 𝒩'` of left differential graded
  `𝒜`-modules, `𝒫 ⊗_𝒜 f` is a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductMap_app_comp_counit`: the
  transformation `t` is compatible with the comparison maps `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩`; at a flat and
  K-flat module, where these are invertible, it is the map `𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'`.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductMap`: **Tag 0FTJ.**

## Implementation notes

The proof is the source's. On a flat and K-flat module `𝒫` the map `𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'`
is a quasi-isomorphism: its cone is `𝒫` tensored with the cone of `ν`, which is acyclic, and
`𝒫` is K-flat. The relative tensor product commutes with cones in its first variable
(`SheafOfModules.TensorFunctorData.coneComplexIso`), so the two factors are interchanged first:
`𝒫 ⊗_𝒜 𝒩 = 𝒩 ⊗_{𝒜^{opp}} 𝒫`, naturally in `𝒩` (`SheafOfModules.RelativeTensor.opSwap_naturality`),
and `𝒫`, read as a left differential graded `𝒜^{opp}`-module, is made a bimodule over
`(𝒜^{opp}, (𝒪, 0))`. Every object of `D(𝒜, d)` is the image of a flat and K-flat module
(Tag 0FSH), so `t` is invertible everywhere.

The hypothesis that `ν` is an isomorphism on cohomology sheaves is
`SheafOfModules.IsCohomologyIso` of the underlying morphism of complexes; the cohomology sheaves
are the homology objects of the complex, so this is `QuasiIso` of that morphism, which is the
form in which the proof uses it.

## References

* [Stacks Project, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules

namespace RelativeTensor

section QuasiIso

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J (Type u)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  {P : DifferentialGradedModule.{u, u, u} A}

/-- **Tensoring a K-flat module with a quasi-isomorphism of right `A.op`-modules, in the second
variable.** For a K-flat right differential graded `A`-module `P` and a quasi-isomorphism
`g : Y ⟶ Y'` of right differential graded `A.op`-modules, the map `P ⊗_A Y ⟶ P ⊗_A Y'` is a
quasi-isomorphism: across the interchange of the two factors it is `g ⊗_{A.op} P`, whose cone is
the cone of `g` tensored with `P`. -/
theorem quasiIso_dgTensorMapLeft_unopLeftMap (hP : IsKFlat P)
    {Y Y' : DifferentialGradedModule.{u, u, u} A.op} (g : Y ⟶ Y')
    (hg : QuasiIso g.toHomologicalComplex) :
    QuasiIso (dgTensorMapLeft P (DifferentialGradedModule.Hom.unopLeftMap g)) := by
  let D' := tensorFunctorDataDgTensorRight P.opLeft.unitBimodule
  have hcone : (DifferentialGradedModule.cone g).complex.Acyclic :=
    (DifferentialGradedModule.acyclic_cone_iff_quasiIso _ g).2 hg
  have hT : (D'.functor.obj (DifferentialGradedModule.cone g)).complex.Acyclic :=
    DifferentialGradedModule.acyclic_dgTensor_opLeft_of_isKFlat hP _ hcone
  have hC : (DifferentialGradedModule.cone (D'.functor.map g)).complex.Acyclic := fun n =>
    (hT n).of_iso (D'.coneComplexIso g).symm
  have h₁ : QuasiIso ((dgTensorFunctor P.opLeft).map g) :=
    (DifferentialGradedModule.acyclic_cone_iff_quasiIso _ _).1 hC
  have sq : (dgTensorFunctor P.opLeft).map g ≫ (dgTensorOpIso P Y').hom =
      (dgTensorOpIso P Y).hom ≫ dgTensorMapLeft P (DifferentialGradedModule.Hom.unopLeftMap g) := by
    ext n : 1
    exact opSwap_naturality P g n
  have h₂ : QuasiIso (dgTensorOpIso P Y').hom := inferInstance
  have : QuasiIso ((dgTensorOpIso P Y).hom ≫
      dgTensorMapLeft P (DifferentialGradedModule.Hom.unopLeftMap g)) := by
    rw [← sq]
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)
  exact quasiIso_of_comp_left (dgTensorOpIso P Y).hom _

omit [HasWeakSheafify J (Type u)] in
/-- Quasi-isomorphy of `P ⊗_A f` depends on `f` only through its underlying morphisms. -/
theorem quasiIso_dgTensorMapLeft_of_heq {L₁ L₁' L₂ L₂' : LeftDifferentialGradedModule.{u, u, u} A}
    (e : L₁ = L₂) (e' : L₁' = L₂') (g₁ : L₁ ⟶ L₁') (g₂ : L₂ ⟶ L₂')
    (h : ∀ n, g₁.toHomologicalComplex.f n ≍ g₂.toHomologicalComplex.f n)
    (hg : QuasiIso (dgTensorMapLeft P g₁)) : QuasiIso (dgTensorMapLeft P g₂) := by
  subst e e'
  obtain rfl : g₁ = g₂ := LeftDifferentialGradedModule.Hom.ext fun n => eq_of_heq (h n)
  exact hg

/-- **Tensoring a K-flat module with a quasi-isomorphism in the second variable.** For a K-flat
right differential graded `A`-module `P` and a quasi-isomorphism `f : L ⟶ L'` of left
differential graded `A`-modules, `P ⊗_A f : P ⊗_A L ⟶ P ⊗_A L'` is a quasi-isomorphism. -/
theorem quasiIso_dgTensorMapLeft (hP : IsKFlat P) {L L' : LeftDifferentialGradedModule.{u, u, u} A}
    (f : L ⟶ L') (hf : QuasiIso f.toHomologicalComplex) : QuasiIso (dgTensorMapLeft P f) :=
  quasiIso_dgTensorMapLeft_of_heq (LeftDifferentialGradedModule.opRight_unopLeft L)
    (LeftDifferentialGradedModule.opRight_unopLeft L')
    (DifferentialGradedModule.Hom.unopLeftMap (LeftDifferentialGradedModule.Hom.opRight f)) f
    (fun _ => HEq.rfl)
    (quasiIso_dgTensorMapLeft_unopLeftMap hP (LeftDifferentialGradedModule.Hom.opRight f) hf)

end QuasiIso

end RelativeTensor

namespace DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {N N' : DifferentialGradedBimodule.{u, u, u} A A'}

/-- The natural transformation `ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'`, `x ⊗ y ↦ x ⊗ ν y`, of functors of
differential graded modules, induced by a homomorphism of bimodules `ν : 𝒩 ⟶ 𝒩'`. -/
noncomputable def tensorDataMap (ν : N ⟶ N') : (tensorData N).functor ⟶ (tensorData N').functor :=
  RelativeTensor.dgTensorRightFunctorMap (C := X.C) (J := X.J) (Osharp := X.O) ν

/-- The natural transformation `ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'` on the homotopy categories, induced by a
homomorphism of bimodules `ν : 𝒩 ⟶ 𝒩'`. -/
noncomputable def homotopyTensorMap (ν : N ⟶ N') :
    HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N') :=
  Quotient.natTransLift _
    { app M := (HomotopyCategory.quotient A').map ((tensorDataMap ν).app M)
      naturality M M₂ ψ := by
        change (HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
              (tensorData N)).map ((HomotopyCategory.quotient A).map ψ) ≫ _ =
            _ ≫ (HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
              (tensorData N')).map ((HomotopyCategory.quotient A).map ψ)
        rw [HomotopyCategory.pullbackTensor_map, HomotopyCategory.pullbackTensor_map,
          idPullbackData_map]
        have hn := congrArg (HomotopyCategory.quotient A').map ((tensorDataMap ν).naturality ψ)
        rw [Functor.map_comp, Functor.map_comp] at hn
        exact hn }

/-- At the image of a differential graded module `ℳ` in the homotopy category,
`homotopyTensorMap ν` is the class of the map `ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'` given by `tensorDataMap ν`. -/
theorem homotopyTensorMap_app (ν : N ⟶ N') (M : DifferentialGradedModule.{u, u, u} A) :
    (homotopyTensorMap ν).app ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A').map ((tensorDataMap ν).app M) :=
  rfl

/-- **The canonical transformation `t : (- ⊗^𝐋_𝒜 𝒩) ⟶ (- ⊗^𝐋_𝒜 𝒩')`** of functors
`D(𝒜, d) ⥤ D(𝒜', d)` induced by a homomorphism `ν : 𝒩 ⟶ 𝒩'` of differential graded
`(𝒜, 𝒜')`-bimodules: the transformation of left derived functors induced by
`ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'`. Its value on a flat and K-flat module `𝒫` is the map
`𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'` (`derivedTensorProductMap_app_comp_counit`). -/
noncomputable def derivedTensorProductMap (ν : N ⟶ N') :
    derivedTensorProduct N ⟶ derivedTensorProduct N' :=
  Functor.leftDerivedNatTrans (derivedTensorProduct N) (derivedTensorProduct N')
    (derivedTensorProductCounit N) (derivedTensorProductCounit N')
    (quasiIsomorphisms.{u, u, u} A)
    (Functor.whiskerRight (homotopyTensorMap ν) (toDerivedCategory.{u, u, u} A'))

/-- **The value of `t`**: the canonical transformation is compatible with the comparison maps
`ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` and the map `ℳ ⊗_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩'`. At a flat and K-flat module, where
the comparison maps are invertible (`isIso_derivedTensorProductCounit_app`), `t` is therefore
the map `𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'`. -/
theorem derivedTensorProductMap_app_comp_counit (ν : N ⟶ N')
    (M : DifferentialGradedModule.{u, u, u} A) :
    (derivedTensorProductMap ν).app
        ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj M)) ≫
        (derivedTensorProductCounit N').app ((HomotopyCategory.quotient A).obj M) =
      (derivedTensorProductCounit N).app ((HomotopyCategory.quotient A).obj M) ≫
        (toDerivedCategory A').map
          ((HomotopyCategory.quotient A').map ((tensorDataMap ν).app M)) := by
  rw [derivedTensorProductMap, Functor.leftDerivedNatTrans_app, Functor.whiskerRight_app,
    homotopyTensorMap_app]
  rfl

/-- At a flat and K-flat module `𝒫` the canonical transformation is invertible when `ν` is an
isomorphism on cohomology sheaves: the map `𝒫 ⊗_𝒜 𝒩 ⟶ 𝒫 ⊗_𝒜 𝒩'` is a quasi-isomorphism. -/
theorem isIso_derivedTensorProductMap_app {ν : N ⟶ N'}
    (qis : IsCohomologyIso ν.toHomologicalComplex)
    {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded
          (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) ∧
      RelativeTensor.IsKFlat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) :
    IsIso ((derivedTensorProductMap ν).app
      ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj P))) := by
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have qν : QuasiIso (DifferentialGradedBimodule.Hom.toLeft ν).toHomologicalComplex :=
    (quasiIso_iff_isIso_homologyMap _).2 fun n => qis n
  have i₁ := isIso_derivedTensorProductCounit_app N hP
  have := isIso_derivedTensorProductCounit_app N' hP
  have hq : QuasiIso ((tensorDataMap ν).app P).toHomologicalComplex :=
    RelativeTensor.quasiIso_dgTensorMapLeft (C := X.C) hP.2
      (DifferentialGradedBimodule.Hom.toLeft ν) qν
  have i₂ : IsIso ((toDerivedCategory A').map
      ((HomotopyCategory.quotient A').map ((tensorDataMap ν).app P))) :=
    isIso_toDerivedCategory_map_of_acyclic_cone A' _ ((acyclic_cone_iff_quasiIso A' _).2 hq)
  have h := derivedTensorProductMap_app_comp_counit ν P
  have : IsIso ((derivedTensorProductMap ν).app
        ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj P)) ≫
      (derivedTensorProductCounit N').app ((HomotopyCategory.quotient A).obj P)) := by
    rw [h]
    exact IsIso.comp_isIso' i₁ i₂
  exact IsIso.of_isIso_comp_right _
    ((derivedTensorProductCounit N').app ((HomotopyCategory.quotient A).obj P))

/-- **Stacks 0FTJ.** Let `(𝒞, 𝒪)` be a ringed site, let `𝒜` and `ℬ` be differential graded
`𝒪`-algebras and let `ν : 𝒩 ⟶ 𝒩'` be a homomorphism of differential graded
`(𝒜, ℬ)`-bimodules which is an isomorphism on cohomology sheaves. Then the canonical
transformation `t : (- ⊗^𝐋_𝒜 𝒩) ⟶ (- ⊗^𝐋_𝒜 𝒩')` is an isomorphism of functors
`D(𝒜, d) ⥤ D(ℬ, d)`. -/
@[stacks 0FTJ]
theorem isIso_derivedTensorProductMap (ν : N ⟶ N') (qis : IsCohomologyIso ν.toHomologicalComplex) :
    IsIso (derivedTensorProductMap ν) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let e := (toDerivedCategory A).objObjPreimageIso Y
  obtain ⟨P, p, hP, hp⟩ :=
    (tensorGood (A := A)).exists_isGood ((toDerivedCategory A).objPreimage Y).as
  have : IsIso ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map p)) :=
    isIso_toDerivedCategory_map_of_acyclic_cone A p ((acyclic_cone_iff_quasiIso A p).2 hp)
  have := isIso_derivedTensorProductMap_app qis hP
  let e' : (toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj P) ≅ Y :=
    asIso ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map p)) ≪≫ e
  have : IsIso ((derivedTensorProduct N).map e'.hom ≫ (derivedTensorProductMap ν).app Y) := by
    rw [(derivedTensorProductMap ν).naturality e'.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedTensorProduct N).map e'.hom) _

end DifferentialGradedModule

end SheafOfModules

end
