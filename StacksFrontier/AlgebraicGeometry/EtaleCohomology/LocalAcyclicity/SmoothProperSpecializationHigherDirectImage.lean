module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecializationUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Specialization maps of the higher direct images of a smooth proper morphism

[Stacks, Lemma 0GKD] says that for `f : X ⟶ S` smooth and proper and `F` a locally constant
abelian sheaf with torsion stalks prime to the residue characteristics, the specialization maps
of the derived stalks of `Rf_* F` are isomorphisms
(`AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional`). The stalk
functors are exact, so the specialization map on the stalks of each cohomology sheaf
`Hⁿ(Rf_* F) = Rⁿ f_* F` is then an isomorphism as well. This file proves that consequence.

The specialization map on derived stalks is the degreewise specialization map on any complex
representing an object (`AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb_app`); if it is
an isomorphism at `K`, the degreewise map is a quasi-isomorphism, and its effect on the `n`-th
cohomology is, up to the identifications `Hⁿ(K_s) ≅ (Hⁿ K)_s` of the exact stalk functors, the
specialization map at `Hⁿ K` (`CategoryTheory.NatTrans.app_homology`).

The derived categories are those of the model `HasDerivedCategory.standard`, in which
[Stacks, Tag 0GKD] is stated; the statements below about sheaves do not mention them.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleSpecializationStalkAb_app_homology`
* `AlgebraicGeometry.isIso_smallEtaleSpecializationStalkAb_app_rightDerived_of_smooth_of_isProper`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **Specialization on derived stalks determines specialization on the stalks of the cohomology
sheaves.** If the specialization map on derived stalks is an isomorphism at `E`, then for every
`n` the specialization map on stalks is an isomorphism at the cohomology sheaf `Hⁿ E`. -/
theorem isIso_smallEtaleSpecializationStalkAb_app_homology (E : smallEtaleDerivedCategory S)
    (h : IsIso ((smallEtaleDerivedSpecializationStalkAb B S hS s t).app E)) (n : ℤ) :
    IsIso ((smallEtaleSpecializationStalkAb B S hS s t).app
      ((DerivedCategory.homologyFunctor _ n).obj E)) := by
  let α := smallEtaleSpecializationStalkAb B S hS s t
  obtain ⟨J, ⟨e⟩⟩ : ∃ J, Nonempty (DerivedCategory.Qh.obj J ≅ E) :=
    ⟨_, ⟨DerivedCategory.Qh.objObjPreimageIso E⟩⟩
  have hJ : IsIso ((smallEtaleDerivedSpecializationStalkAb B S hS s t).app
      (DerivedCategory.Qh.obj J)) := by
    exact (NatTrans.isIso_app_iff_of_iso _ e).2 h
  rw [smallEtaleDerivedSpecializationStalkAb_app] at hJ
  let ψ := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J.as
  let A := (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.app J
  let C := (smallEtaleStalkAb
    (t.hom ≫ strictHenselizationToBase B S hS s)).mapDerivedCategoryFactorsh.app J
  have hJ' :
      IsIso (A.hom ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ) ≫ C.inv) :=
    hJ
  have h1 : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ) ≫ C.inv) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ A.hom _ _ hJ'
  have h2 : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ C.inv (Iso.isIso_inv C) h1
  have hψ : QuasiIso ψ := (HomotopyCategory.quotient_map_mem_quasiIso_iff ψ).1
    ((DerivedCategory.isIso_Qh_map_iff _).1 h2)
  have h3 : IsIso (HomologicalComplex.homologyMap ψ n) :=
    (quasiIsoAt_iff_isIso_homologyMap ψ n).1 (hψ.quasiIsoAt n)
  have h4 : IsIso (α.app (J.as.homology n)) := by
    change IsIso (α.app (J.as.sc n).homology)
    rw [NatTrans.app_homology α (J.as.sc n)]
    have h3' : IsIso (ShortComplex.homologyMap ((J.as.sc n).mapNatTrans α)) := h3
    infer_instance
  let i : (DerivedCategory.homologyFunctor _ n).obj E ≅ J.as.homology n :=
    (DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactorsh _ n).app J ≪≫
        (HomotopyCategory.homologyFunctorFactors _ _ n).app J.as
  exact (NatTrans.isIso_app_iff_of_iso α i).2 h4

/-- **[Stacks, Tag 0GKD] on the higher direct images.** Let `f : X ⟶ S` be smooth and proper and
`F` a locally constant abelian sheaf on `X_étale` whose stalks are torsion of orders prime to the
residue characteristics. Then for every geometric point `s` of `S`, every geometric point `t` of
the strict henselization of `S` at `s` and every `q`, the specialization map
`sp : (Rᵠ f_* F)_s ⟶ (Rᵠ f_* F)_t` is an isomorphism. -/
@[sga "1 XIII 1.14" "special case", sga "4 XVI 2.3" "special case"]
theorem isIso_smallEtaleSpecializationStalkAb_app_rightDerived_of_smooth_of_isProper
    {X : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ S) [Smooth f] [IsProper f]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (q : ℕ) :
    IsIso ((smallEtaleSpecializationStalkAb B S hS s t).app
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F)) := by
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  let α := smallEtaleSpecializationStalkAb B S hS s t
  have h0 := isIso_specializationMap_of_smooth_of_isProper_unconditional B hX hS f F hFlc hFtors s t
  have h1 := isIso_smallEtaleSpecializationStalkAb_app_homology B S hS s t _ h0 (q : ℤ)
  let i : (DerivedCategory.homologyFunctor _ (q : ℤ)).obj ((smallEtaleDerivedPushforwardAb f).obj
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)) ≅
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F :=
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforwardAb f)
      (smallEtaleDerivedPushforwardAb f) (smallEtaleDerivedPushforwardAbUnit f)
      (fun K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ =>
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) F q
  exact (NatTrans.isIso_app_iff_of_iso α i).1 h1

end

end AlgebraicGeometry

end
