module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.KunnethFlatSheaves
public import StacksFrontier.Algebra.Homology.TotalSingleShiftedQuasiIso

/-!
# The inputs of [Stacks, Tag 0FU4] at modules placed in arbitrary degrees

[Stacks, Tag 0FU4] is proved in `StacksDraft.AlgebraicGeometry.BaseChange.FlatKunneth` for two
modules placed in degree zero, by chaining the projection formula of [Stacks, Tag 08EU], flat
base change ([Stacks, Tag 0A1D]) and Tor vanishing ([Stacks, Tag 0GMU]).  The proof of
[Stacks, Tag 0FLT] reduces to complexes concentrated in a single degree, but in *every* degree,
because its dévissage moves the degree.  This file supplies the chain at `ℱ[-i]` and `𝒢[-j]`.

* Tor vanishing is proved for an arbitrary complex `K` in the first factor against a complex
  isomorphic to `ℬ[-j]` in the second, through a K-flat resolution of `K` and the identification
  of the total complex against a shifted single complex with the shifted row complex
  (`Stacks.TotalSingleShift.quasiIso_mapBifunctorMap_single_of_rowQuasiIso`).
* Flat base change is the chart argument of
  `AlgebraicGeometry.FlatKunneth.isIso_derivedBaseChangeComp_single_of_isQuasicoherent`, which
  applies verbatim to a module placed in any degree.

## Main results

* `AlgebraicGeometry.FlatKunneth.isIso_derivedTensor_derivedPullbackNatTrans_toTensor_ofIsoSingle`
* `AlgebraicGeometry.FlatKunneth.isIso_derivedBaseChangeComp_singleObj_of_isQuasicoherent`
* `AlgebraicGeometry.FlatKunneth.isIso_kunnethMap_comp_toTensor_singleObj`: **the relative
  Künneth map of [Stacks, Tag 0FLP] at `ℱ[-i]` and `𝒢[-j]`, followed by the derived-to-ordinary
  comparisons, is invertible** for `a`, `b` quasi-compact and quasi-separated and `𝒢` flat over
  `S`.

## References

* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.FlatKunneth

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- Dropping an identity factor from the middle of a composite. -/
private theorem eq_of_comp_id_comp {C : Type*} [Category C] {a b c : C} {x : a ⟶ b}
    {i : b ⟶ b} {y : b ⟶ c} {z : a ⟶ c} (hi : i = 𝟙 b) (h : x ≫ i ≫ y = z) : x ≫ y = z := by
  rw [hi, Category.id_comp] at h
  exact h

/-- Cancelling an invertible map on the left of a commuting square. -/
private theorem isIso_comp_of_square {C : Type*} [Category C] {a b c d e : C}
    (x : a ⟶ b) (v : b ⟶ d) (s : a ⟶ c) (t : c ⟶ d) (r : d ⟶ e) (h : x ≫ v = s ≫ t)
    (hx : IsIso x) (hs : IsIso s) (ht : IsIso (t ≫ r)) : IsIso (v ≫ r) := by
  have : IsIso (x ≫ v ≫ r) := by
    rw [← Category.assoc, h, Category.assoc]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hs ht
  exact IsIso.of_isIso_comp_left x (v ≫ r)

section RingedSpaces

variable {X W : RingedSpace.{u, u}} (p : W ⟶ X)
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tor vanishing against a module for which `p^*(-) ⊗ ℬ` is exact, in every degree.**  For
an arbitrary complex `K` of `𝒪_X`-modules and a complex `L` isomorphic to `ℬ` placed in degree
`j`, the derived-to-ordinary pullback comparison in the first factor followed by the
derived-to-ordinary tensor comparison,

`Lp^*K ⊗^𝐋 L ⟶ p^*K ⊗^𝐋 L ⟶ Tot(p^*K ⊗ L)`,

is an isomorphism.  `p` is not assumed flat. -/
theorem isIso_derivedTensor_derivedPullbackNatTrans_toTensor_ofIsoSingle
    (B : SheafOfModules.{u} (structureSheafRing W))
    [PreservesFiniteLimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ) (j : ℤ)
    (eL : L ≅ (HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj B) :
    IsIso (((derivedTensorProductFunctor W.sheaf).map ((derivedPullbackNatTrans p).app K)).app
        (DerivedCategory.Q.obj L) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor ((pullbackComplex p).obj K) L) := by
  have := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} W.sheaf
  have : ∀ M : SheafOfModules.{u} (structureSheafRing W),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).Additive :=
    fun M => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
      (J := Opens.grothendieckTopology W.carrier) W.sheaf M
  obtain ⟨P, π, hP, -, hπ, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X K
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
  -- termwise, `p^*π ⊗ ℬ` is the exact functor `p^*(-) ⊗ ℬ` applied to `π`
  have hrow : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
      ((pullbackComplex p).map π) B) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π (modulePullback p ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).flip.obj B)
  have htot : QuasiIso (HomologicalComplex.mapBifunctorMap ((pullbackComplex p).map π) (𝟙 L)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) (ComplexShape.up ℤ)) :=
    Stacks.TotalSingleShift.quasiIso_mapBifunctorMap_of_iso_single
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
      ((pullbackComplex p).map π) L B j eL hrow
  -- the derived tensor product of the K-flat `p^*P` with `L` is the total tensor complex
  have hP' := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional p P hP
  have h0 : IsIso ((canonicalDerivedTensorProduct W.sheaf).toTensor
      ((pullbackComplex p).obj P) L) := by
    exact (congrArg IsIso ((canonicalDerivedTensorProduct W.sheaf).toTensor_eq_comparisonLeft
      _ L hP')).mpr inferInstance
  have hn := eq_of_comp_id_comp
    ((congrArg (fun t => ((canonicalDerivedTensorProduct W.sheaf).tensor.obj
        (DerivedCategory.Q.obj ((pullbackComplex p).obj K))).map t)
      (CategoryTheory.Functor.map_id DerivedCategory.Q L)).trans
      (CategoryTheory.Functor.map_id _ _))
    ((canonicalDerivedTensorProduct W.sheaf).toTensor_naturality
      ((pullbackComplex p).map π) (𝟙 L))
  have hQtot := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 htot
  have ht : IsIso (((canonicalDerivedTensorProduct W.sheaf).tensor.map
        (DerivedCategory.Q.map ((pullbackComplex p).map π))).app (DerivedCategory.Q.obj L) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor ((pullbackComplex p).obj K) L) := by
    rw [hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 hQtot
  -- the square of the comparison `Lp^* ⟶ p^*` along `π`
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 hπ
  have : IsIso ((derivedPullbackNatTrans p).app P) :=
    Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app p P hP
  let G := (derivedTensorProductFunctor W.sheaf).flip.obj (DerivedCategory.Q.obj L)
  exact isIso_comp_of_square (G.map ((derivedPullback p).map (DerivedCategory.Q.map π)))
    (G.map ((derivedPullbackNatTrans p).app K)) (G.map ((derivedPullbackNatTrans p).app P))
    (G.map (DerivedCategory.Q.map ((pullbackComplex p).map π)))
    ((canonicalDerivedTensorProduct W.sheaf).toTensor ((pullbackComplex p).obj K) L)
    ((G.map_comp _ _).symm.trans
      ((congrArg G.map ((derivedPullbackNatTrans p).naturality π)).trans (G.map_comp _ _)))
    inferInstance inferInstance ht

end RingedSpaces

section Schemes

open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight kunnethMap kunnethBaseChangeLeg)

/-- **Tor vanishing on a fibre product, in every degree.**  For morphisms of schemes
`a : X ⟶ S` and `b : Y ⟶ S`, a quasi-coherent `𝒪_Y`-module `𝒢` flat over `S`, any complex `K` of
`𝒪_X`-modules and a complex `L` isomorphic to `q^*𝒢` placed in degree `j`, with `p`, `q` the
projections of `X ×_S Y`, the canonical map `Lp^*K ⊗^𝐋 L ⟶ Tot(p^*K ⊗ L)` is an isomorphism. -/
theorem isIso_derivedTensor_derivedPullbackNatTrans_toTensor_fibre {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [G.IsQuasicoherent] (hG : IsFlatOver b.toLRSHom.toShHom G)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing (pullback a b).toRingedSpace)) ℤ)
    (j : ℤ) (eL : L ≅ (HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj
      ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G)) :
    IsIso (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).map
          ((derivedPullbackNatTrans (pullback.fst a b).toLRSHom.toShHom).app K)).app
        (DerivedCategory.Q.obj L) ≫
      (canonicalDerivedTensorProduct (pullback a b).toRingedSpace.sheaf).toTensor
        ((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj K) L) := by
  have hex : exactFunctor _ _ (modulePullback (pullback.fst a b).toLRSHom.toShHom ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (pullback a b).toRingedSpace.sheaf).flip.obj
        ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G)) :=
    Stacks.AlgebraicGeometry.ModuleBaseChange.exact_totalCoefficients
      (IsPullback.of_hasPullback a b) G hG
  have := ((exactFunctor_iff _).1 hex).1
  have := ((exactFunctor_iff _).1 hex).2
  exact isIso_derivedTensor_derivedPullbackNatTrans_toTensor_ofIsoSingle
    (pullback.fst a b).toLRSHom.toShHom _ K L j eL

/-- The terms of a quasi-coherent module placed in degree `j` are quasi-coherent. -/
theorem isQuasicoherent_singleObj_X {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j i : ℤ) :
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj M).X i).IsQuasicoherent := by
  by_cases hi : i = j
  · subst hi
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).symm inferInstance
  · have := isFinitePresentation_of_isZero _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j M i hi)
    exact isQuasicoherent_of_isFinitePresentation _

/-- The terms of a module flat over the base placed in degree `j` are flat over the base. -/
theorem isFlatOver_singleObj_X {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (hM : IsFlatOver f.toLRSHom.toShHom M) (j i : ℤ) :
    IsFlatOver f.toLRSHom.toShHom
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj M).X i) := by
  by_cases hi : i = j
  · subst hi
    rw [isFlatOver_iff_of_moduleIso f.toLRSHom.toShHom
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M)]
    exact hM
  · exact isFlatOver_of_isZero f _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j M i hi)

/-- A quasi-coherent module placed in degree `j` has quasi-coherent cohomology sheaves. -/
theorem isQCohAll_Q_singleObj {W : Scheme.{u}} (M : W.Modules) [M.IsQuasicoherent] (j : ℤ) :
    IsQCohAll (DerivedCategory.Q.obj
      ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) j).obj M)) := by
  intro k
  have e := (DerivedCategory.homologyFunctorFactors W.Modules k).app
    ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) j).obj M)
  by_cases h0 : k = j
  · subst h0
    exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
      (e ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm inferInstance
  · have := isFinitePresentation_of_isZero
      ((HomologicalComplex.homologyFunctor W.Modules (ComplexShape.up ℤ) k).obj
        ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) j).obj M))
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) j M k h0)
    exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso e.symm
      (isQuasicoherent_of_isFinitePresentation _)

/-- **Flat base change for a quasi-coherent module placed in any degree.**  For a cartesian
square of schemes with `f` quasi-compact and quasi-separated and a quasi-coherent `𝒪_X`-module
`ℱ` flat over `S`, the composition `Lg^*Rf_*(ℱ[-j]) ⟶ Rf'_*L(g')^*(ℱ[-j]) ⟶ Rf'_*(g')^*(ℱ[-j])`
is an isomorphism.  The proof is that of
`AlgebraicGeometry.FlatKunneth.isIso_derivedBaseChangeComp_single_of_isQuasicoherent`. -/
theorem isIso_derivedBaseChangeComp_singleObj_of_isQuasicoherent {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (j : ℤ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj F))
            ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj F))) := by
  have hGqcoh : ∀ n : ℤ,
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj F).X n).IsQuasicoherent :=
    fun n => isQuasicoherent_singleObj_X F j n
  have hchart := isIso_derivedBaseChangeComp_totalTensor_of_charts hsq
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)))
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj F)
    (Stacks.SheafOfModules.isKFlat_single_unit X.toRingedSpace.sheaf)
    (fun n => Stacks.Blowup.isQuasicoherent_homology_Q_single X _
      (isQuasicoherent_of_isFinitePresentation
        (_root_.SheafOfModules.unit X.ringCatSheaf)) n)
    hGqcoh
    (fun U V hU hV hUV => kFlat_sectionsComplex_pullback_fromSpec f hU hV hUV
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) j).obj F)
      ((CochainComplex.minus_iff _).2 ⟨j, inferInstance⟩) hGqcoh
      (isFlatOver_singleObj_X f F hflat j))
  refine (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) ?_).1 hchart
  exact Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.toRingedSpace.sheaf _ _ ≪≫
    Stacks.SheafOfModules.tensorComplexUnitIso X.toRingedSpace.sheaf _

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The relative Künneth map at modules placed in arbitrary degrees.**  Let `a : X ⟶ S` and
`b : Y ⟶ S` be quasi-compact and quasi-separated, let `p`, `q` be the projections of
`X ×_S Y`, and let `ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat over `S`.  For all
`i` and `j` the relative Künneth map of [Stacks, Tag 0FLP] at `ℱ[-i]` and `𝒢[-j]`, followed by
`R(p ≫ a)_*` of the derived-to-ordinary comparisons

`Lp^*(ℱ[-i]) ⊗^𝐋 Lq^*(𝒢[-j]) ⟶ p^*(ℱ[-i]) ⊗^𝐋 q^*(𝒢[-j]) ⟶ Tot(p^*(ℱ[-i]) ⊗ q^*(𝒢[-j]))`,

is an isomorphism. -/
theorem isIso_kunnethMap_comp_toTensor_singleObj
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hG : IsFlatOver b.toLRSHom.toShHom G) (i j : ℤ) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
        (pullback.snd a b).toLRSHom.toShHom
        ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom) rfl
        (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b)
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))
        (DerivedCategory.Q.obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))
            ≫
      (derivedPushforward ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom)).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
            ((derivedPullbackNatTrans (pullback.fst a b).toLRSHom.toShHom).app
                ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F) ×ₘ
              (derivedPullbackNatTrans (pullback.snd a b).toLRSHom.toShHom).app
                ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) ≫
          (canonicalDerivedTensorProduct (pullback a b).toRingedSpace.sheaf).toTensor
            ((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj
              ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))
            ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
              ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)))) := by
  have hF0 := isQCohAll_Q_singleObj F i
  have hG0 := isQCohAll_Q_singleObj G j
  have hqG : ((Scheme.Modules.pullback (pullback.snd a b)).obj G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ G
  let eL : (pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj
        ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (modulePullback (pullback.snd a b).toLRSHom.toShHom) (ComplexShape.up ℤ) j).app G
  have hqG0 : IsQCohAll (DerivedCategory.Q.obj
      ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))) := by
    have h := isQCohAll_Q_singleObj ((Scheme.Modules.pullback (pullback.snd a b)).obj G) j
    intro k
    exact (SheafOfModules.isQuasicoherent (pullback a b).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ k).mapIso (DerivedCategory.Q.mapIso eL)).symm (h k)
  -- the projection formula of Tag 08EU at `a`
  have h1 := isIso_adjunctionTensorMap_of_quasicoherent a _ hF0
    ((derivedPushforward b.toLRSHom.toShHom).obj _)
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward b hG0)
  -- the interchanged projection formula at `p`
  have h3 := isIso_adjunctionTensorMapRight_of_quasicoherent (pullback.fst a b) inferInstance
    inferInstance _ _ hqG0 hF0
  -- base change for the `S`-flat `𝒢`, with the ordinary pullback on the right
  have h2 : IsIso (kunnethBaseChangeLeg a.toLRSHom.toShHom
      b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b)
      (DerivedCategory.Q.obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) ≫
      (derivedPushforward (pullback.fst a b).toLRSHom.toShHom).map
        ((derivedPullbackNatTrans (pullback.snd a b).toLRSHom.toShHom).app
          ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))) := by
    have hbc := isIso_derivedBaseChangeComp_singleObj_of_isQuasicoherent b a (pullback.fst a b)
      (pullback.snd a b) (IsPullback.of_hasPullback a b).flip G hG j
    exact (congrArg (fun t => IsIso (t ≫ _))
      (Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg_eq_derivedBaseChangeMap _ _ _ _ _
        _)).mpr hbc
  have hk := isIso_kunnethMap_comp_tensorMap a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) _ _
    ((derivedPullbackNatTrans (pullback.snd a b).toLRSHom.toShHom).app
      ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) h1 h2 h3
  -- Tor vanishing against `q^*𝒢` placed in degree `j`
  have : SheafOfModules.IsQuasicoherent
      (show SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) from G) :=
    inferInstanceAs G.IsQuasicoherent
  have h4 := isIso_derivedTensor_derivedPullbackNatTrans_toTensor_fibre a b G hG
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F)
    ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
      ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) j eL
  exact (congrArg (fun z => IsIso (_ ≫ (derivedPushforward
      ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom)).map z))
    (Category.assoc _ _ _)).mpr (isIso_comp_map_bifunctor _ _ _ _ _ _ hk h4)

end Schemes

end AlgebraicGeometry.FlatKunneth

end
