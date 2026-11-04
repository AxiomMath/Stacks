module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.TorDiagonal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves

/-!
# Tor vanishing against a module flat over the source of the pullback

Let `p : W ⟶ X` be a morphism of ringed spaces and `ℬ` an `𝒪_W`-module such that the functor
`ℱ ↦ p^*ℱ ⊗_{𝒪_W} ℬ` from `𝒪_X`-modules to `𝒪_W`-modules is exact.  Then for every
`𝒪_X`-module `ℱ` the canonical map

`Lp^*(ℱ[0]) ⊗^𝐋_{𝒪_W} ℬ[0] ⟶ (p^*ℱ ⊗_{𝒪_W} ℬ)[0]`

is an isomorphism: the derived-to-ordinary pullback comparison of [Stacks, Tag 06YJ] in the first
factor, followed by the derived-to-ordinary tensor comparison of [Stacks, Tag 06YU].  For a
morphism of schemes and a quasi-coherent `ℬ` flat over `X` the functor is exact by
[Stacks, Tag 0GMU]; that is the case of the two projections of a fibre product `X ×_S Y` and
`ℬ = q^*𝒢` for `𝒢` flat over `S`, which is where flatness of `𝒢` enters the Künneth formula of
[Stacks, Tag 0FU4].

`p` is not assumed flat, and neither comparison is invertible on its own: `Lp^*ℱ` need not be
concentrated in degree zero.

## Main results

* `AlgebraicGeometry.FlatKunneth.isIso_derivedTensor_pullbackSingleComparison_toTensor`: the
  statement above, at a ringed-space morphism with the exactness as an instance argument.
* `AlgebraicGeometry.FlatKunneth.isIso_tensorMap_toTensor_single_of_rowQuasiIso`: the transport
  step, along a morphism that is a quasi-isomorphism after `- ⊗ ℬ` termwise.
* `AlgebraicGeometry.FlatKunneth.isIso_derivedTensor_pullbackSingleComparison_toTensor_fibre`:
  its instance at the first projection of `X ×_S Y` and `ℬ = q^*𝒢`, for `𝒢` quasi-coherent and
  flat over `S`.

## Implementation notes

Choose a K-flat resolution `π : P ⟶ ℱ[0]`.  The derived pullback is computed by `p^*P`
([Stacks, Tag 06YJ]), so the first comparison is, up to isomorphisms, `Q(p^*π)`; and `p^*P` is
K-flat ([Stacks, Tag 06YC]), so the derived tensor product with `ℬ[0]` is the total tensor
complex.  By naturality of the derived-to-ordinary tensor comparison the composite is therefore
the class of `Tot(p^*π ⊗ ℬ[0])`, which is termwise the functor `p^*(-) ⊗ ℬ` applied to `π` and
hence a quasi-isomorphism by exactness.  `p^*π` itself is not a quasi-isomorphism, which is why
`Stacks.Intersection.Diagonal.isIso_toTensor_single_pullback`, stated for a flat `p`, does not
apply as it stands.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.GlobalKunneth (pullbackSingleComparison singleC singleD)

universe u

namespace AlgebraicGeometry.FlatKunneth

attribute [local instance 10000] HasDerivedCategory.standard

section RingedSpaces

variable {X W : RingedSpace.{u, u}} (p : W ⟶ X)
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport of the derived-to-ordinary tensor comparison against `ℬ[0]` along a morphism
`φ : K ⟶ K'` which becomes a quasi-isomorphism after `- ⊗ ℬ` is applied termwise: if the
comparison at `K` is invertible, then so is `φ ⊗^𝐋 ℬ[0]` followed by the comparison at `K'`.
`φ` itself need not be a quasi-isomorphism. -/
theorem isIso_tensorMap_toTensor_single_of_rowQuasiIso
    {K K' : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules W.sheaf) ℤ} (φ : K ⟶ K')
    (B : Stacks.DerivedTensor.RingedSite.Modules W.sheaf)
    (hrow : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) φ B))
    (hK : IsIso ((canonicalDerivedTensorProduct W.sheaf).toTensor K
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))) :
    IsIso (((canonicalDerivedTensorProduct W.sheaf).tensor.map (DerivedCategory.Q.map φ)).app
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor K'
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) := by
  have := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} W.sheaf
  let L := (HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules W.sheaf)
    (ComplexShape.up ℤ) 0).obj B
  have htot : QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) (ComplexShape.up ℤ)) := by
    have h2 : QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) (ComplexShape.up ℤ) ≫
        (CochainComplex.KFlatBifunctor.totalSingleIso
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) K' B).hom) := by
      rw [CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) φ B]
      infer_instance
    exact (quasiIso_iff_comp_right _ _).1 h2
  have hn := (canonicalDerivedTensorProduct W.sheaf).toTensor_naturality φ (𝟙 L)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hn
  rw [hn]
  exact IsIso.comp_isIso' hK ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 htot)

omit [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The comparison `Lp^*(QK) ⟶ Q(p^*K)` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at a complex, with the trivial
identification of the two homotopy-category functors removed. -/
theorem derivedPullbackNatTrans_app_eq
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app K =
      (derivedPullback p).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (derivedPullbackComparison p).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have h1 : (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app K =
      (derivedPullback p).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (derivedPullbackComparison p).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((modulePullback p).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := rfl
  have hm : DerivedCategory.Qh.map
      (((modulePullback p).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map (Quotient.lift.isLift_hom _ _ _ _)).trans
      (DerivedCategory.Qh.map_id _)
  rw [h1, hm]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.id_comp _)

omit [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The derived-to-ordinary pullback comparison on a module in degree zero is the component of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at `ℱ[0]`, followed by the
identification of the degreewise pullback of `ℱ[0]` with `(p^*ℱ)[0]`. -/
theorem pullbackSingleComparison_eq (F : SheafOfModules.{u} (structureSheafRing X)) :
    pullbackSingleComparison p F =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app (singleC F) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (modulePullback p)
            (ComplexShape.up ℤ) 0).app F).hom := by
  refine Eq.trans ?_ (congrArg (fun t => t ≫ DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (modulePullback p)
      (ComplexShape.up ℤ) 0).app F).hom) (derivedPullbackNatTrans_app_eq p (singleC F)).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ t) (Category.assoc _ _ _).symm)
  rfl

/-- Termwise `- ⊗ ℬ` applied to `p^*π` followed by an isomorphism is a quasi-isomorphism when
`π` is one and `p^*(-) ⊗ ℬ` is exact. -/
theorem quasiIso_rowComplexMap_pullbackComplex_map_comp
    (B : SheafOfModules.{u} (structureSheafRing W))
    [PreservesFiniteLimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    {P Q : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {R : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ}
    (π : P ⟶ Q) [QuasiIso π]
    (e : (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).obj Q ≅ R) :
    QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
      ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).map π ≫ e.hom) B) := by
  have := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} W.sheaf
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj
      B).Additive :=
    Functor.flip_obj_additive (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) B
  have : (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B).Additive := by
    have : PreservesBinaryBiproducts (modulePullback p ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj
        B).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hrow₁ : QuasiIso ((modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj
        B).mapHomologicalComplex (ComplexShape.up ℤ) |>.map π) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π _
  have hrow₂ : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) e.hom B) := by
    have : IsIso (CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) e.hom B) :=
      Iso.isIso_hom ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj
        B).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e)
    exact quasiIso_of_isIso _
  have hc : CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
        ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).map π ≫ e.hom) B =
        ((modulePullback p ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj
            B).mapHomologicalComplex (ComplexShape.up ℤ)).map π ≫
          CochainComplex.KFlatBifunctor.rowComplexMap
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) e.hom B := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map
        ((modulePullback p).map (π.f n) ≫ e.hom.f n)).app B =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map
        ((modulePullback p).map (π.f n))).app B ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map (e.hom.f n)).app B
    exact NatTrans.congr_app
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).map_comp _ _) B
  rw [hc]
  exact quasiIso_comp (hφ := hrow₁) (hφ' := hrow₂) _ _

omit [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Naturality of the derived-to-ordinary pullback comparison on `ℱ[0]` against a morphism
`π : P ⟶ ℱ[0]`: it is the comparison at `P` followed by the class of `p^*π`. -/
theorem derivedPullback_map_comp_pullbackSingleComparison
    (F : SheafOfModules.{u} (structureSheafRing X))
    {P : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (π : P ⟶ singleC F) :
    (derivedPullback p).map (DerivedCategory.Q.map π) ≫ pullbackSingleComparison p F =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app P ≫
        DerivedCategory.Q.map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).map π ≫
          ((HomologicalComplex.singleMapHomologicalComplex (modulePullback p)
            (ComplexShape.up ℤ) 0).app F).hom) := by
  refine (congrArg (fun t => _ ≫ t) (pullbackSingleComparison_eq p F)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _)
    ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).naturality π)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => _ ≫ t) (DerivedCategory.Q.map_comp _ _).symm

/-- The components of `T.map f` are isomorphisms when `f` is. -/
private theorem isIso_map_app_of_isIso {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) {Y Z : C} (f : Y ⟶ Z) (hf : IsIso f) (A : D) :
    IsIso ((T.map f).app A) :=
  ((T.mapIso (@asIso _ _ _ _ f hf)).app A).isIso_hom

/-- **Tor vanishing against a module for which `p^*(-) ⊗ ℬ` is exact.**  The derived-to-ordinary
pullback comparison in the first factor followed by the derived-to-ordinary tensor comparison,

`Lp^*(ℱ[0]) ⊗^𝐋 ℬ[0] ⟶ (p^*ℱ)[0] ⊗^𝐋 ℬ[0] ⟶ Tot((p^*ℱ)[0] ⊗ ℬ[0])`,

is an isomorphism for every `𝒪_X`-module `ℱ`.  `p` is not assumed flat. -/
theorem isIso_derivedTensor_pullbackSingleComparison_toTensor
    (B : SheafOfModules.{u} (structureSheafRing W))
    [PreservesFiniteLimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F)).app
        (singleD B) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor
        (singleC ((modulePullback p).obj F)) (singleC B)) := by
  have := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} W.sheaf
  obtain ⟨P, π, hP, -, hπ, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X
    (singleC F)
  let π' : (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).obj P ⟶
      singleC ((modulePullback p).obj F) :=
    (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).map π ≫
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback p)
        (ComplexShape.up ℤ) 0).app F).hom
  -- the derived tensor product of the K-flat `p^*P` with `ℬ[0]` is the total tensor complex
  have hP' := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional p P hP
  have h0 : IsIso ((canonicalDerivedTensorProduct W.sheaf).toTensor
      ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex p).obj P)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) := by
    rw [(canonicalDerivedTensorProduct W.sheaf).toTensor_eq_comparisonLeft _ _ hP']
    infer_instance
  -- the first comparison is, up to isomorphisms, the class of `π'`
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 hπ
  have hi := Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app p P hP
  have hx : IsIso ((derivedPullback p).map (DerivedCategory.Q.map π)) := Functor.map_isIso _ _
  have hc' : pullbackSingleComparison p F =
      (@asIso _ _ _ _ ((derivedPullback p).map (DerivedCategory.Q.map π)) hx).inv ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app P ≫
          DerivedCategory.Q.map π' :=
    (Iso.eq_inv_comp _).2 (derivedPullback_map_comp_pullbackSingleComparison p F π)
  let DT := derivedTensorProductFunctor W.sheaf
  have hE : (DT.map (pullbackSingleComparison p F)).app (singleD B) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor
        (singleC ((modulePullback p).obj F)) (singleC B) =
      (DT.map (@asIso _ _ _ _ ((derivedPullback p).map (DerivedCategory.Q.map π)) hx).inv).app
          (singleD B) ≫
        (DT.map ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans p).app P)).app
          (singleD B) ≫
        ((DT.map (DerivedCategory.Q.map π')).app (singleD B) ≫
          (canonicalDerivedTensorProduct W.sheaf).toTensor
            (singleC ((modulePullback p).obj F)) (singleC B)) := by
    refine (congrArg (fun z => (DT.map z).app (singleD B) ≫ _) hc').trans ?_
    refine (congrArg (· ≫ _) (NatTrans.congr_app (DT.map_comp _ _) (singleD B))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    refine (congrArg (· ≫ _) (NatTrans.congr_app (DT.map_comp _ _) (singleD B))).trans ?_
    exact Category.assoc _ _ _
  refine (congrArg IsIso hE).mpr ?_
  exact IsIso.comp_isIso' (isIso_map_app_of_isIso DT _ (Iso.isIso_inv _) _)
    (IsIso.comp_isIso' (isIso_map_app_of_isIso DT _ hi _)
      (isIso_tensorMap_toTensor_single_of_rowQuasiIso π' B
        (quasiIso_rowComplexMap_pullbackComplex_map_comp p B π _) h0))

end RingedSpaces

/-- **Tor vanishing on a fibre product against a module flat over the base.**  For morphisms of
schemes `a : X ⟶ S` and `b : Y ⟶ S`, a quasi-coherent `𝒪_Y`-module `𝒢` flat over `S` and any
`𝒪_X`-module `ℱ`, with `p`, `q` the projections of `X ×_S Y`, the canonical map

`Lp^*(ℱ[0]) ⊗^𝐋 (q^*𝒢)[0] ⟶ Tot((p^*ℱ)[0] ⊗ (q^*𝒢)[0])`

is an isomorphism.  The exactness of `p^*(-) ⊗ q^*𝒢` is [Stacks, Tag 0GMU], `q^*𝒢` being flat
over `X` by [Stacks, Tag 01U8]. -/
theorem isIso_derivedTensor_pullbackSingleComparison_toTensor_fibre {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [G.IsQuasicoherent] (hG : IsFlatOver b.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    IsIso (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).map
          (pullbackSingleComparison (pullback.fst a b).toLRSHom.toShHom F)).app
        (singleD ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G)) ≫
      (canonicalDerivedTensorProduct (pullback a b).toRingedSpace.sheaf).toTensor
        (singleC ((modulePullback (pullback.fst a b).toLRSHom.toShHom).obj F))
        (singleC ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G))) := by
  have hex : exactFunctor _ _ (modulePullback (pullback.fst a b).toLRSHom.toShHom ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (pullback a b).toRingedSpace.sheaf).flip.obj
        ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G)) :=
    Stacks.AlgebraicGeometry.ModuleBaseChange.exact_totalCoefficients
      (IsPullback.of_hasPullback a b) G hG
  have := ((exactFunctor_iff _).1 hex).1
  have := ((exactFunctor_iff _).1 hex).2
  exact isIso_derivedTensor_pullbackSingleComparison_toTensor
    (pullback.fst a b).toLRSHom.toShHom _ F

end AlgebraicGeometry.FlatKunneth

end
