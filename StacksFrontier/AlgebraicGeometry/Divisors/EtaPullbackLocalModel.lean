module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackFlatTerms
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedEmptySupport

/-!
# The comparison of décalages under a pullback, computed on a local model

Let `g : V ⟶ U` be a morphism of schemes and `D ⊆ U` an effective Cartier divisor whose pullback
along `g` is defined.  The derived comparison of décalages
`Stacks.Divisors.Eta.divisorPullbackEtaKFlatComparison` at a K-flat complex `P^•` of flat modules
is an isomorphism as soon as it is one at a single K-flat complex `N^•` of flat modules isomorphic
to `P^•` in the derived category: the two are connected by a roof of quasi-isomorphisms out of a
K-flat complex of flat modules, along which being an isomorphism transfers.

Read through a K-flat resolution of the décalage, this says that the chain-level comparison
precomposed with the resolution is a quasi-isomorphism, which is the form the local step of the
proof of Stacks 0F9X consumes.

## Main results

* `Stacks.Divisors.Eta.exists_kFlat_roof`: an isomorphism in the derived category between two
  complexes is realized by two quasi-isomorphisms out of a K-flat complex of flat modules.
* `Stacks.Divisors.Eta.quasiIso_divisorPullbackEtaMap_of_model`: the local step.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.IdealTorsion.Eta (etaObj pullbackComplex pullbackComplexMap)

universe u

namespace Stacks.Divisors.Eta

attribute [local instance] Stacks.Divisors.Eta.etaHasDerivedCategory

/-- **An isomorphism in the derived category is a roof of quasi-isomorphisms out of a K-flat
complex of flat modules.**  It is a right fraction `[s]⁻¹ ≫ [g]` (calculus of fractions in the
homotopy category), and the source of the fraction has a K-flat resolution by flat modules
(Stacks 06YF). -/
theorem exists_kFlat_roof (Z : RingedSpace.{u})
    {P₁ P₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ}
    (e : DerivedCategory.Q.obj P₁ ≅ DerivedCategory.Q.obj P₂) :
    ∃ (T : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ)
      (s : T ⟶ P₁) (t : T ⟶ P₂), QuasiIso s ∧ QuasiIso t ∧
        Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z T ∧
        ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf) (T.X n) := by
  obtain ⟨X', s, hs, g, hfac⟩ := DerivedCategory.right_fac e.hom
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  have hg : IsIso (DerivedCategory.Q.map g) := by
    have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
      rw [hfac, IsIso.hom_inv_id_assoc]
    rw [this]; infer_instance
  have hg' : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).1 hg
  obtain ⟨T, p, hTk, hTflat, hp, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Z X'
  exact ⟨T, p ≫ s, p ≫ g, inferInstance, inferInstance, hTk, hTflat⟩

variable {V U : Scheme.{u}} (g : V ⟶ U) (D : U.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] [hD : Stacks.Divisors.IsPullbackDefined g D]

/-- **The local step.**  Let `P^•` be a K-flat complex of flat `𝒪_U`-modules and `r : R^• ⟶
η_{ℐ_D} P^•` a quasi-isomorphism out of a K-flat complex.  If `P^•` is isomorphic in the derived
category to a K-flat complex `N^•` of flat modules at which the derived comparison of décalages
is an isomorphism, then the chain-level comparison precomposed with `g^* r` is a
quasi-isomorphism. -/
theorem quasiIso_divisorPullbackEtaMap_of_model
    (P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := U.toRingedSpace.sheaf) (P.X n))
    (hPk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace P)
    {R : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ}
    (r : R ⟶ @etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP)) [QuasiIso r]
    (hR : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace R)
    (N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hN : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := U.toRingedSpace.sheaf) (N.X n))
    (hNk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace N)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj N)
    (hiso : IsIso (divisorPullbackEtaKFlatComparison g D N hN)) :
    QuasiIso (pullbackComplexMap g.toLRSHom.toShHom r ≫ divisorPullbackEtaMap g D P hP) := by
  rw [← isIso_divisorPullbackEtaKFlatComparison_iff g D P hP r hR]
  obtain ⟨T, s, t, hs, ht, hTk, hTflat⟩ := exists_kFlat_roof U.toRingedSpace e
  rw [← isIso_divisorPullbackEtaKFlatComparison_iff_of_quasiIso g D s hTflat hP hTk hPk]
  rw [isIso_divisorPullbackEtaKFlatComparison_iff_of_quasiIso g D t hTflat hN hTk hNk]
  exact hiso

/-! ### Off the divisor -/

/-- The first projection of the fibre product defining a term of the décalage is an isomorphism
when the ideal inclusion is: the second leg of the cospan, the inclusion of consecutive ideal
powers, is then an isomorphism. -/
theorem isIso_etaFst_of_isIso (Z : RingedSpace.{u})
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))) ℤ) (n : ℤ) :
    IsIso (Stacks.IdealTorsion.Eta.etaFst Z I ι F n) := by
  have := Stacks.IdealTorsion.Eta.isIso_idealPowerIncl_of_isIso Z I ι n (F.X (n + 1))
  exact pullback_fst_iso_of_right_iso _ _

/-- **Off the divisor the derived comparison of décalages is an isomorphism**: if `D` has empty
support then both ideal inclusions are invertible, the décalages are the complexes themselves,
and the chain-level comparison is an isomorphism because the first projections of the fibre
products defining the décalages are. -/
theorem isIso_divisorPullbackEtaKFlatComparison_of_supportSet_eq_empty
    (hD0 : D.supportSet = ∅)
    (P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := U.toRingedSpace.sheaf) (P.X n))
    (hPk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace P) :
    IsIso (divisorPullbackEtaKFlatComparison g D P hP) := by
  have hι : IsIso (idealSheafι D) := isIso_idealSheafι_of_supportSet_eq_empty D hD0
  have hι' : IsIso (idealSheafι (D.comap g)) :=
    isIso_idealSheafι_of_supportSet_eq_empty (D.comap g)
      (supportSet_comap_eq_empty D g (fun y => by rw [hD0]; exact Set.notMem_empty _))
  -- the comparison of Stacks 06YJ at the décalage, which is the complex itself
  let e := @Stacks.IdealTorsion.Eta.etaObjIsoSelf U.toRingedSpace (idealSheaf D) (idealSheafι D)
    (mono_idealSheafι D) hι (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP)
  have hcP := Stacks.IdealTorsion.Eta.isIso_etaPullbackComparisonOnComplex
    g.toLRSHom.toShHom P hPk
  have hsq := Stacks.IdealTorsion.Eta.etaPullbackComparisonOnComplex_naturality
    g.toLRSHom.toShHom e.hom
  have hc : IsIso (Stacks.IdealTorsion.Eta.etaPullbackComparisonOnComplex g.toLRSHom.toShHom
      (@etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
        (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP))) := by
    have : IsIso (pullbackComplexMap g.toLRSHom.toShHom e.hom) :=
      (((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso e).isIso_hom
    have : IsIso (Stacks.IdealTorsion.Eta.etaPullbackComparisonOnComplex g.toLRSHom.toShHom
        (@etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
          (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP)) ≫
        DerivedCategory.Q.map (pullbackComplexMap g.toLRSHom.toShHom e.hom)) := by
      rw [← hsq]; infer_instance
    exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map
      (pullbackComplexMap g.toLRSHom.toShHom e.hom))
  -- the chain-level comparison is an isomorphism, degree by degree
  have hm : IsIso (divisorPullbackEtaMap g D P hP) := by
    suffices hcomp : ∀ n : ℤ, IsIso ((divisorPullbackEtaMap g D P hP).f n) from
      HomologicalComplex.Hom.isIso_of_components _
    intro n
    have h1 := @isIso_etaFst_of_isIso V.toRingedSpace (idealSheaf (D.comap g))
      (idealSheafι (D.comap g)) hι' (isInvertible_idealSheaf (D.comap g))
      (pullbackComplex g.toLRSHom.toShHom P) n
    have h2 := @isIso_etaFst_of_isIso U.toRingedSpace (idealSheaf D) (idealSheafι D) hι
      (isInvertible_idealSheaf D) P n
    have hfst := @Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_f_fst _ _
      g.toLRSHom.toShHom
      (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
      (idealSheaf (D.comap g)) (idealSheafι (D.comap g)) (isInvertible_idealSheaf (D.comap g))
      (Stacks.Divisors.pullbackIdealSheafComapIso g D hD) (mono_idealSheafι D)
      (mono_pullbackIdealIncl_of_isPullbackDefined g D inferInstance) (mono_idealSheafι (D.comap g))
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι g D hD) P
      (isIdealTorsionFree_X D P hP) (isIdealTorsionFree_pullbackComplex_X' g D P hP)
      (isIdealTorsionFree_pullbackComplex_X g D P hP) n
    have h3 : IsIso ((divisorPullbackEtaMap g D P hP).f n ≫
        Stacks.IdealTorsion.Eta.etaFst V.toRingedSpace (idealSheaf (D.comap g))
          (idealSheafι (D.comap g)) (pullbackComplex g.toLRSHom.toShHom P) n) := by
      rw [divisorPullbackEtaMap, hfst]
      exact @IsIso.comp_isIso' _ _ _ _ _ _ _
        (@Functor.map_isIso _ _ _ _ _ _ (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom)
          _ h2) (Iso.isIso_hom _)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Stacks.IdealTorsion.Eta.etaFst V.toRingedSpace
      (idealSheaf (D.comap g)) (idealSheafι (D.comap g)) (pullbackComplex g.toLRSHom.toShHom P) n)
      h1 h3
  have : IsIso (DerivedCategory.Q.map (divisorPullbackEtaMap g D P hP)) := inferInstance
  exact IsIso.comp_isIso' hc this

end Stacks.Divisors.Eta

end
