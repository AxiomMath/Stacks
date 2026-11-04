module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportLeray
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeCorner
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportTopExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule

/-!
# Top compactly supported cohomology along a family of curves

Let `k` be a separably closed field, `N` a positive integer and `Λ = ℤ/N`. For `f : U → S` and
`q : S → Spec k` separated of finite type, with compactifications, the Leray isomorphism
`RΓ_c(U, Λ) ≅ RΓ_c(S, Rf_! Λ)` and the corner of its spectral sequence give, when the
compactification of `S` has dimension at most `d` and `Rf_! Λ` lives in degrees `[0, 2]`,

`H^{2d+2}_c(U, Λ) ≅ H^{2d}_c(S, R²f_! Λ)`.

This is the count of the top compactly supported cohomology of a smooth variety through an
elementary fibration, in the proof of Poincaré duality: `R²f_! Λ ≅ Λ_S` for an elementary
fibration, and `H^{2d}_c(S, Λ) ≅ Λ` by induction on the dimension.

## Main results

* `Stacks.EtaleCohomology.isLE_compactlySupportedCohomology_single`: `RΓ_c(S, M[-q])` lives in
  degrees `≤ q + 2d`.
* `Stacks.EtaleCohomology.nonempty_compactlySupportedCohomologyGroup_top_iso`: the corner,
  `H^{2d+2}(RΓ_c(S, K)) ≅ H^{2d}(RΓ_c(S, H²(K)))` for `K` in degrees `[0, 2]`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category (`Stacks.EtaleCohomology.compactlySupportedCohomology`), which is therefore a
local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.CompositeDegreeVanishing

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ]

/-- `Hⁿ(G(M[-q])) ≅ H^{n'}(G(M))` for `n' = n - q`, for a functor `G` commuting with the
shift. -/
def homologyObjSingleIso (M : C) (n q n' : ℤ) (h : -q + n = n') :
    (DerivedCategory.homologyFunctor D n).obj
        (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M)) ≅
      (DerivedCategory.homologyFunctor D n').obj
        (G.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)) :=
  (DerivedCategory.homologyFunctor D n).mapIso
      (G.mapIso (((DerivedCategory.Plus.singleFunctors C).shiftIso (-q) q 0 (by omega)).app M).symm
        ≪≫ (G.commShiftIso (-q)).app _) ≪≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso (-q) n n' h).app _

end Stacks.CompositeDegreeVanishing

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {k : Type u} [Field k] {S : Scheme.{u}} (fS : S ⟶ Spec (.of k))
  [LocallyOfFiniteType fS] [QuasiCompact fS] [IsSeparated fS]
  (jS : CompactificationOf (Over.mk fS)) (N : ℕ) [NeZero N]

omit [LocallyOfFiniteType fS] [QuasiCompact fS] [IsSeparated fS] in
/-- **`RΓ_c(S, M[-q])` lives in degrees `≤ q + 2d`** when the compactification of `S` has
dimension at most `d` (Tag 095U on the compactification). -/
theorem isLE_compactlySupportedCohomology_single [IsSepClosed k] (d : ℕ)
    (hd : topologicalKrullDim jS.space ≤ d) (M : EtaleModules.{u, 0} (ZMod N) S) (q : ℤ) :
    (DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, 0} k fS jS (ZMod N)).obj
      ((DerivedCategory.Plus.singleFunctor _ q).obj M))).IsLE (q + (2 * d : ℕ)) := by
  let e₁ : (DerivedCategory.Plus.singleFunctor _ q).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M) ≅
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj
        ((DerivedCategory.Plus.singleFunctor _ q).obj M) :=
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion) q).app M
  let e₂ := (rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, 0} (ZMod N) jS.toBase)
    (etaleModuleGlobalSections.{u, 0} (ZMod N) (Spec (.of k)))
    (etaleModuleGlobalSections.{u, 0} (ZMod N) jS.space)
    (etaleModuleGlobalSectionsDirectImageIso jS.toBase (ZMod N))).symm
  have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
    (etaleModuleGlobalSections.{u, 0} (ZMod N) jS.space)
    ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M) (2 * d : ℕ) q
    (fun p hp => by
      have hp' : 2 * d < p := by exact_mod_cast hp
      refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
        (etaleModuleGlobalSections.{u, 0} (ZMod N) jS.space) (m := (p : ℤ)) rfl _).1 ?_
      have hs := subsingleton_ext_constantModuleSheaf_zmod_of_proper jS.toBase d hd N
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M) p hp'
      have : Subsingleton ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf
          (ZMod N) jS.space.smallEtaleTopology) p).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M)) := hs
      let e := etaleModuleRightDerivedPlusIsoExt (ZMod N) jS.space
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M) p
      have : Subsingleton ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).obj
          (((etaleModuleGlobalSections.{u, 0} (ZMod N) jS.space).rightDerivedPlus (p : ℤ)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M))) :=
        e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
      exact ModuleCat.isZero_of_subsingleton _)
  have h' : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod N) jS.space).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ q).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj M)))) (q + (2 * d : ℕ)) :=
    h
  exact DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Plus.ι.mapIso
    ((e₂.app _).symm ≪≫ (etaleModuleDerivedGlobalSections.{u, 0} (ZMod N) (Spec (.of k))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) jS.toBase).mapIso e₁))) _

omit [LocallyOfFiniteType fS] [QuasiCompact fS] [IsSeparated fS] in
/-- **The corner of the Leray spectral sequence in top degree**: if the compactification of `S`
has dimension at most `d` and `K` lives in degrees `[0, 2]`, then
`H^{2d+2}(RΓ_c(S, K)) ≅ H^{2d}(RΓ_c(S, H²(K)))`. -/
theorem nonempty_compactlySupportedCohomologyGroup_top_iso [IsSepClosed k] (d : ℕ)
    (hd : topologicalKrullDim jS.space ≤ d)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) S)) [K.IsGE 0] [K.IsLE 2] :
    Nonempty ((compactlySupportedCohomologyGroup.{u, 0} k fS jS (ZMod N) (2 * d + 2)).obj K ≅
      (compactlySupportedCohomologyGroup.{u, 0} k fS jS (ZMod N) (2 * d)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((DerivedCategory.Plus.homologyFunctor _ 2).obj K))) := by
  let G := compactlySupportedCohomology.{u, 0} k fS jS (ZMod N) ⋙ DerivedCategory.Plus.ι
  let t := DerivedCategory.Plus.TStructure.t (C := EtaleModules.{u, 0} (ZMod N) S)
  have hG : ∀ (M : EtaleModules.{u, 0} (ZMod N) S) (q j : ℤ), 2 * (d : ℤ) < j - q →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj
        (G.obj ((DerivedCategory.Plus.singleFunctor _ q).obj M))) := fun M q j hj =>
    DerivedCategory.isZero_of_isLE _ (q + (2 * d : ℕ)) j (by omega)
      (hX := isLE_compactlySupportedCohomology_single fS jS N d hd M q)
  have hiso := Stacks.CompositeDegreeVanishing.isIso_homology_map_truncGEπ_of_isLE G (2 * d)
    hG K 1 2 (by simpa using ‹K.IsGE 0›)
  let T := (t.truncGE 2).obj K
  have hT : ∀ i : ℤ, i ≠ 2 → IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj T) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.Plus.isZero_homology_of_isGE T 2 i h
    · have := DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app 2 i (by omega) K
      exact (DerivedCategory.Plus.isZero_homology_of_isLE K 2 i h).of_iso
        (asIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((t.truncGEπ 2).app K))).symm
  have : T.IsLE 2 := by
    rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
    exact fun i hi => hT i (by omega)
  obtain ⟨M, ⟨e⟩⟩ := Stacks.BoundedCohomologicalDimension.exists_iso_plus_singleFunctor_obj T 2
  let eT : T ≅ (DerivedCategory.Plus.singleFunctor _ 2).obj
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj T) :=
    e ≪≫ (DerivedCategory.Plus.singleFunctor _ 2).mapIso
      (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := EtaleModules.{u, 0} (ZMod N) S) 2).app M).symm ≪≫
        ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso e).symm)
  have := DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app 2 2 le_rfl K
  exact ⟨@asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ (2 * d + 2)).map
      (G.map ((t.truncGEπ 2).app K))) hiso
    ≪≫ (DerivedCategory.homologyFunctor _ (2 * d + 2)).mapIso
      (G.mapIso (eT ≪≫ (DerivedCategory.Plus.singleFunctor _ 2).mapIso
        (asIso ((DerivedCategory.Plus.homologyFunctor _ 2).map ((t.truncGEπ 2).app K))).symm)) ≪≫
    Stacks.CompositeDegreeVanishing.homologyObjSingleIso G _ (2 * d + 2) 2 (2 * d) (by ring)⟩

section Leray

variable {U : Scheme.{u}} (f : U ⟶ S) [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S]
  [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f] {g : U ⟶ Spec (.of k)}
  [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g] (hg : f ≫ fS = g)
  (jf : CompactificationOf (Over.mk f)) (j : CompactificationOf (Over.mk g))

omit [QuasiCompact fS] in
include hg in
/-- **`H^{2d+2}_c(U) ≅ H^{2d}_c(S, R²f_! Λ)`, read in `Ext`.** For `f : U → S` and
`f_S : S → Spec k` separated of finite type over a separably closed field, with compactifications
`j_f` (fibres of dimension at most one), `j_S` (of dimension at most `d`) and `j` (of
`g = f_S ∘ f`),
the Leray isomorphism `RΓ_c(U, Λ) ≅ RΓ_c(S, Rf_! Λ)` and the corner of its spectral sequence
(`Rf_! Λ` lives in degrees `[0, 2]`) identify `Ext^{2d+2}_{Ū}(Λ, j_! Λ_U)` with
`H^{2d}_c(S, R²f_! Λ)`; if `R²f_! Λ ≅ Λ_S`, this is `Ext^{2d}_{S̄}(Λ, (j_S)_! Λ_S)`. -/
theorem nonempty_ext_top_addEquiv_of_higherDirectImage_two_iso [IsSepClosed k] (d : ℕ)
    (hd : topologicalKrullDim jS.space ≤ d)
    (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
    (hR2 : Nonempty ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := U) N))) ≅ ExtensionTorsor.unitSheaf (X := S) N)) :
    Nonempty (Ext (ExtensionTorsor.unitSheaf (X := j.space) N)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j.immersion).obj
          (ExtensionTorsor.unitSheaf (X := U) N)) (2 * d + 2) ≃+
      Ext (ExtensionTorsor.unitSheaf (X := jS.space) N)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj
          (ExtensionTorsor.unitSheaf (X := S) N)) (2 * d)) := by
  subst hg
  obtain ⟨eR⟩ := hR2
  let L₀ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod N) U) 0).obj
    (ExtensionTorsor.unitSheaf (X := U) N)
  have hL₀ : isTorsionPlus.{u, 0} (ZMod N) U L₀ := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (NeZero.pos N) (ZMod.natCast_self N) _
  let K := (derivedLowerShriek.{u, 0} f jf (ZMod N)).obj L₀
  have : K.IsGE 0 := isGE_derivedLowerShriek_obj (ZMod N) f jf L₀ 0
  have : K.IsLE 2 := by
    have h := isLE_derivedLowerShriek_of_isTorsionPlus (ZMod N) f jf 1 hf L₀ hL₀ 0 inferInstance
    rwa [DerivedCategory.Plus.isLE_ι_obj_iff,
      show (0 : ℤ) + ((2 * 1 : ℕ) : ℤ) = 2 by norm_num] at h
  obtain ⟨eC⟩ := nonempty_compactlySupportedCohomologyGroup_top_iso fS jS N d hd K
  let eL := (compactlySupportedCohomologyGroupLerayIso k f fS jf jS j (ZMod N)
    (2 * d + 2)).app ⟨L₀, hL₀⟩
  have e₁ := compactlySupportedCohomologyGroupSingleIsoExt (ZMod N) k (f ≫ fS) j
    (ExtensionTorsor.unitSheaf (X := U) N) (2 * d + 2)
  have e₂ := compactlySupportedCohomologyGroupSingleIsoExt (ZMod N) k fS jS
    (ExtensionTorsor.unitSheaf (X := S) N) (2 * d)
  rw [show ((2 * d + 2 : ℕ) : ℤ) = 2 * (d : ℤ) + 2 by push_cast; ring] at e₁
  rw [show ((2 * d : ℕ) : ℤ) = 2 * (d : ℤ) by push_cast; ring] at e₂
  exact ⟨(e₁.symm ≪≫ (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).mapIso
    (eL ≪≫ eC ≪≫ (compactlySupportedCohomologyGroup.{u, 0} k fS jS (ZMod N) (2 * d)).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eR)) ≪≫ e₂).addCommGroupIsoToAddEquiv⟩

end Leray

end Stacks.EtaleCohomology

end
