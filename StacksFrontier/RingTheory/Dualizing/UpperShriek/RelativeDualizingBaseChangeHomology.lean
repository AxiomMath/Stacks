module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChangeVanishing

/-!
# The base change of a relative dualizing complex, after restriction to the polynomial algebra

Let `R → A` be a flat finite type homomorphism with `R` Noetherian, let `R → R'` be any
homomorphism and set `A' = R' ⊗_R A`.  Let `P = R[x_1, …, x_n] → A` be a polynomial presentation
and `P' = R'[x_1, …, x_n] → A'` its base change.  This file proves that `ω^•_{A/R} ⊗_A^L A'` and
`ω^•_{A'/R'}` become isomorphic in `D(P')`, and hence that their cohomology modules are isomorphic
as `A'`-modules.  This is the cohomological content of case (2) of [Stacks, Tag 0BZV].

## Main results

* `Dualizing.nonempty_restrictScalars_upperShriekFunctor_unit_iso` — `ω^•_{B/S}` read over the
  polynomial algebra of a presentation is `Hom^•(F, L)[n]` for every bounded above complex of
  projectives `F` representing `B` and every complex `L` representing the polynomial algebra.
* `Dualizing.nonempty_restrictScalars_derivedBaseChange_relativeDualizing_iso` — the isomorphism
  in `D(P')`.
* `Dualizing.nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra` — the
  isomorphism of cohomology modules in `ModuleCat A'`.

## Implementation notes

Flatness of `A` makes `A` perfect over `P` with a finite projective resolution `F`, and
`ω^•_{A/R}` read over `P` is `Hom^•_P(F, P)[n]`
(`Dualizing.exists_projectiveResolution_relativeDualizingComplex_iso`).  On the one hand, by the
Tor-independent base change of [Stacks, Tag 0661] for the pushout square `P, A, P', A'`, the
restriction to `P'` of `ω^•_{A/R} ⊗_A^L A'` is `Hom^•_P(F, P) ⊗_P^L P'[n]`, which is
`Hom^•_{P'}(F ⊗_P P', P')[n]` because `F` is a bounded complex of finite projectives.  On the other
hand `F ⊗_P P'` resolves `A'` (`Dualizing.nonempty_extendScalars_resolution_iso`), so
`ω^•_{A'/R'}` read over `P'` is the same Hom complex by [Stacks, Tag 0A66].  No identification of
`A'`-linear structures in the derived category is involved; on cohomology modules the
`A'`-linearity is automatic because `P' → A'` is surjective.

## References

* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The regular module of the target, read along the presenting surjection, is the lift of the
target to the module universe read there. -/
private noncomputable def singleRestrictScalarsULiftIso {S B : Type u} [CommRing S] [CommRing B]
    {φ : S →+* B} (q : PolynomialPresentation φ) :
    (ModuleCat.restrictScalars.{u} q.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} q.Poly) 0).obj
        ((ModuleCat.restrictScalars q.toRingHom).obj (ModuleCat.of B (ULift.{u} B))) :=
  ((ModuleCat.restrictScalars.{u} q.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of B B) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} q.Poly) 0).mapIso
      ((ModuleCat.restrictScalars.{u} q.toRingHom).mapIso
        (LinearEquiv.toModuleIso (ULift.moduleEquiv.{u, u, u} (R := B) (M := B)).symm))

/-- **The relative dualizing complex over the polynomial algebra, at any projective resolution.**
Let `q : S[x_1, …, x_n] → B` present `φ : S → B`, let `F` be a bounded above complex of projective
`S[x]`-modules representing `B`, and `L` a complex representing `S[x]`.  Then `ω^•_{B/S} = φ^!(S)`,
read over `S[x]`, is `Hom^•(F, L)[n]`. -/
theorem nonempty_restrictScalars_upperShriekFunctor_unit_iso {S B : Type u} [CommRing S]
    [CommRing B] {φ : S →+* B} (q : PolynomialPresentation φ)
    (F : CochainComplex (ModuleCat.{u} q.Poly) ℤ) (b : ℤ) [F.IsStrictlyLE b]
    [∀ i, Projective (F.X i)]
    (eF : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} q.Poly) 0).obj
      ((ModuleCat.restrictScalars q.toRingHom).obj (ModuleCat.of B (ULift.{u} B))))
    (L : CochainComplex (ModuleCat.{u} q.Poly) ℤ)
    (eL : DerivedCategory.Q.obj L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} q.Poly) 0).obj (ModuleCat.of q.Poly q.Poly)) :
    Nonempty ((ModuleCat.restrictScalars.{u} q.toRingHom).mapDerivedCategory.obj
        (q.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S))) ≅
      (DerivedCategory.Q.obj (CochainComplex.HomComplexR q.Poly F L))⟦(q.variableCount : ℤ)⟧) := by
  let P := q.Poly
  let U := ModuleCat.restrictScalars.{u} q.toRingHom
  let n : ℤ := q.variableCount
  let Punit := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let e' : U.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) ≅
      DerivedCategory.Q.obj F := singleRestrictScalarsULiftIso q ≪≫ eF.symm
  let eHom : (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom P).obj
      (Opposite.op (U.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))), Punit) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR P F L) :=
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := P)).hom.mapIso
        (e'.symm.op.prod eL.symm) ≪≫
      StacksDraft.DerivedHom.projectiveHomComparison.iso F L b
  exact ⟨U.mapDerivedCategory.mapIso ((shiftFunctor (DerivedCategory (ModuleCat.{u} B)) n).mapIso
        ((derivedHom.{u, 0, u} q.toRingHom).mapIso q.derivedExtensionUnitIso)) ≪≫
      (U.mapDerivedCategory.commShiftIso n).app ((derivedHom.{u, 0, u} q.toRingHom).obj Punit) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} P)) n).mapIso
        ((nonempty_modelHomIsoRestrictScalarsDerivedHom q.toRingHom Punit).some.symm ≪≫ eHom)⟩

/-- **Tor-independent base change of `Hom^•(F, P)[n]`.**  Let `P, A, P', T` be a pushout square
with `A` and `P'` Tor independent over `P`, and `F` a bounded complex of finite projective
`P`-modules.  If `ω ∈ D(A)` restricts to `Hom^•_P(F, P)[n]` in `D(P)`, then for every left-derived
model of extension of scalars along `A → T`, the restriction of `ω ⊗_A^L T` to `D(P')` is
`Hom^•_{P'}(F ⊗_P P', P')[n]`. -/
theorem nonempty_restrictScalars_derivedBaseChange_homComplexR_iso {P A P' T : Type u}
    [CommRing P] [CommRing A] [CommRing P'] [CommRing T] [Algebra P A] [Algebra P P']
    [Algebra P T] [Algebra A T] [Algebra P' T] [IsScalarTower P A T] [IsScalarTower P P' T]
    [Algebra.IsPushout P A P' T] (hTor : RingTheory.TorIndependence.TorIndependent P A P')
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} T))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A T)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (F : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ) [∀ j, Module.Finite P (F.X j)]
    [∀ j, Module.Projective P (F.X j)] [F.IsStrictlyLE 0] [F.IsStrictlyGE (-n)]
    (ω : DerivedCategory (ModuleCat.{u} A))
    (eG : (ModuleCat.restrictScalars.{u} (algebraMap P A)).mapDerivedCategory.obj ω ≅
      (DerivedCategory.Q.obj (CochainComplex.HomComplexR P F
        ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P))))⟦n⟧) :
    Nonempty ((ModuleCat.restrictScalars.{u} (algebraMap P' T)).mapDerivedCategory.obj
        (bcT.obj ω) ≅
      (DerivedCategory.Q.obj (CochainComplex.HomComplexR P'
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap P P')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap P P')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)))))⟦n⟧) := by
  let f := algebraMap P P'
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let Hc := CochainComplex.HomComplexR P F J
  have hHcLE : CochainComplex.IsStrictlyLE Hc n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have : Subsingleton (F.X (-j)) :=
      ModuleCat.isZero_iff_subsingleton.mp (F.isZero_of_isStrictlyGE (-n) (-j) (by omega))
    exact (homComplexUnitTermLinearEquiv F j).injective.subsingleton
  have hHcproj : ∀ j, Projective (Hc.X j) := fun j => by
    have : Module.Projective P (Hc.X j) :=
      Module.Projective.of_equiv (homComplexUnitTermLinearEquiv F j).symm
    infer_instance
  let DP := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  let cmp := @RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u}
      P A P' T _ _ _ _ _ _ _ _ (algebraMap P A) f (algebraMap A T) (algebraMap P' T)
      ((IsScalarTower.algebraMap_eq P A T).symm.trans (IsScalarTower.algebraMap_eq P P' T))
      DP.functor bcT DP.comparison cmpT DP.isLeftDerived ldT
  have hcmp : IsIso cmp.2.1 :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u,
      u, u} P A P' T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTor
      DP.functor bcT DP.comparison cmpT DP.isLeftDerived ldT
  exact ⟨(asIso (cmp.2.1.app ω)).symm ≪≫ DP.functor.mapIso eG ≪≫
    (DP.functor.commShiftIso n).app (DerivedCategory.Q.obj Hc) ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} P')) n).mapIso
      (@asIso _ _ _ _ (DP.comparison.app Hc) (DP.comparison_isIso_of_projective Hc n) ≪≫
        DerivedCategory.Q.mapIso
          (StacksDraft.RelativelyPerfect.homComplexBaseChangeIsoOfProjective f F J 0 0))⟩

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

/-- The base-changed presentation lies over the original one: `P → P' → A'` is `P → A → A'`. -/
theorem baseChange_toRingHom_comp_map (p : PolynomialPresentation (algebraMap R A)) :
    (p.baseChange (R' := R')).toRingHom.comp
        (MvPolynomial.map (σ := Fin p.variableCount) (algebraMap R R')) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom.comp
        p.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro s
    have hp : p.toRingHom (MvPolynomial.C s) = algebraMap R A s :=
      RingHom.congr_fun p.commutes s
    have hp' : (p.baseChange (R' := R')).toRingHom (MvPolynomial.C (algebraMap R R' s)) =
        algebraMap R R' s ⊗ₜ[R] (1 : A) :=
      RingHom.congr_fun (p.baseChange (R' := R')).commutes (algebraMap R R' s)
    change (p.baseChange (R' := R')).toRingHom
        (MvPolynomial.map (algebraMap R R') (MvPolynomial.C s)) =
      (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.C s)
    rw [MvPolynomial.map_C, hp', hp, ← mul_one (algebraMap R R' s), ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  · intro i
    exact (congrArg (p.baseChange (R' := R')).toRingHom (MvPolynomial.map_X _ i)).trans
      (MvPolynomial.eval₂Hom_X' _ _ i)

/-- **`ω^•_{A'/R'}` over the base-changed polynomial algebra.**  Let `R → A` be flat, presented
by `p`, and `F` a bounded above complex of projective `P`-modules representing `A`.  Then
`ω^•_{A'/R'}` read over `P'` is `Hom^•_{P'}(F ⊗_P P', P')[n]`. -/
theorem nonempty_restrictScalars_upperShriekFunctor_baseChange_unit_iso [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (F : CochainComplex (ModuleCat.{u} p.Poly) ℤ)
    [F.IsStrictlyLE 0] [∀ i, Projective (F.X i)]
    (eF : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) :
    letI : Algebra p.Poly (p.baseChange (R' := R')).Poly := MvPolynomial.algebraMvPolynomial
    Nonempty ((ModuleCat.restrictScalars.{u}
        (p.baseChange (R' := R')).toRingHom).mapDerivedCategory.obj
        ((p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) ≅
      (DerivedCategory.Q.obj (CochainComplex.HomComplexR (p.baseChange (R' := R')).Poly
        (((ModuleCat.extendScalars.{u, u, u}
          (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)
        (((ModuleCat.extendScalars.{u, u, u}
          (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
                (ModuleCat.of p.Poly p.Poly)))))⟦(p.variableCount : ℤ)⟧) := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let f := algebraMap P P'
  let E := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  have hF'LE : CochainComplex.IsStrictlyLE (E.obj F) 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (ModuleCat.extendScalars.{u, u, u} f).map_isZero (F.isZero_of_isStrictlyLE 0 j hj)
  have hF'proj : ∀ j, Projective ((E.obj F).X j) := fun j =>
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).map_projective _ inferInstance
  obtain ⟨eF'⟩ := nonempty_extendScalars_resolution_iso (R' := R') p F 0 eF
  let eJ' : DerivedCategory.Q.obj (E.obj J) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} P') 0).obj (ModuleCat.of P' P') :=
    DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} f)
          (ComplexShape.up ℤ) 0).app (ModuleCat.of P P)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (extendScalarsUnitIso f)
  exact @nonempty_restrictScalars_upperShriekFunctor_unit_iso _ _ _ _ _ (p.baseChange (R' := R'))
    (E.obj F) 0 hF'LE hF'proj eF' (E.obj J) eJ'

/-- **`ω^•_{A/R} ⊗_A^L A'` and `ω^•_{A'/R'}` agree over the polynomial algebra.**  Let `R` be
Noetherian, `R → A` flat of finite type presented by `p`, and `R → R'` arbitrary, with
`A' = R' ⊗_R A` and `P' → A'` the base-changed presentation.  For every left-derived model of
extension of scalars along `A → A'`, the restrictions to `D(P')` of `ω^•_{A/R} ⊗_A^L A'` and of
`ω^•_{A'/R'}` are isomorphic. -/
theorem nonempty_restrictScalars_derivedBaseChange_relativeDualizing_iso [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    Nonempty ((ModuleCat.restrictScalars.{u}
        (p.baseChange (R' := R')).toRingHom).mapDerivedCategory.obj
        (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
      (ModuleCat.restrictScalars.{u} (p.baseChange (R' := R')).toRingHom).mapDerivedCategory.obj
        ((p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')))) := by
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let T := TensorProduct R R' A
  let P := MvPolynomial (Fin p.variableCount) R
  let p' := p.baseChange (R' := R')
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let f := algebraMap P P'
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra A T := Algebra.TensorProduct.rightAlgebra
  let : Algebra P' T := p'.toRingHom.toAlgebra
  let : Algebra P T := (p'.toRingHom.comp f).toAlgebra
  have hmap : f = MvPolynomial.map (algebraMap R R') := MvPolynomial.algebraMap_def
  have : IsScalarTower P P' T := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower P A T := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change p'.toRingHom (f x) = (Algebra.TensorProduct.includeRight :
      A →ₐ[R] TensorProduct R R' A) (p.toRingHom x)
    rw [hmap]
    exact RingHom.congr_fun (baseChange_toRingHom_comp_map (R' := R') p) x)
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq (fun r ↦
    (RingHom.congr_fun p.commutes r).symm)
  have : IsScalarTower R' P' T := IsScalarTower.of_algebraMap_eq (fun r ↦
    (RingHom.congr_fun p'.commutes r).symm)
  have : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A T, IsScalarTower.algebraMap_apply P A T,
      ← IsScalarTower.algebraMap_apply R P A])
  have : IsScalarTower R P' T := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R R' T, IsScalarTower.algebraMap_apply R' P' T,
      ← IsScalarTower.algebraMap_apply R R' P'])
  have : Algebra.IsPushout R P R' P' := (inferInstance : Algebra.IsPushout R R' P P').symm
  have : Algebra.IsPushout R A R' T :=
    Algebra.IsPushout.symm (TensorProduct.isPushout (R := R) (S := R') (T := A))
  have : Algebra.IsPushout P A P' T :=
    (Algebra.IsPushout.comp_iff R P (T := A) R' P' (T' := T)).1 inferInstance
  have hTor : RingTheory.TorIndependence.TorIndependent R A R' := by
    rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
    intro i hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact isZero_Tor_succ_of_flat (ModuleCat.of R A) (ModuleCat.of R R') k
  have hTorP : RingTheory.TorIndependence.TorIndependent P A P' :=
    torIndependent_mvPolynomialBaseChange p.variableCount p.toAlgHom hTor
  obtain ⟨F, hfp, hGE, hLE, ⟨eF⟩, ⟨eG⟩⟩ :=
    exists_projectiveResolution_relativeDualizingComplex_iso p
  have (j : ℤ) := (hfp j).1
  have (j : ℤ) := (hfp j).2
  obtain ⟨eL⟩ :=
    nonempty_restrictScalars_derivedBaseChange_homComplexR_iso hTorP bcT cmpT ldT F _ _ eG
  obtain ⟨eR⟩ := nonempty_restrictScalars_upperShriekFunctor_baseChange_unit_iso (R' := R') p F eF
  exact ⟨eL ≪≫ eR.symm⟩

/-- Along a surjective ring map, restriction of scalars reflects isomorphy of modules: a linear
isomorphism over the source between two restricted modules is linear over the target. -/
theorem nonempty_iso_of_restrictScalars_iso_of_surjective {S T : Type u} [CommRing S]
    [CommRing T] (φ : S →+* T) (hφ : Function.Surjective φ) {M N : ModuleCat.{u} T}
    (e : (ModuleCat.restrictScalars.{u} φ).obj M ≅ (ModuleCat.restrictScalars.{u} φ).obj N) :
    Nonempty (M ≅ N) :=
  ⟨LinearEquiv.toModuleIso
    { toFun := fun m => e.hom.hom m
      invFun := fun n => e.inv.hom n
      map_add' := fun x y => e.hom.hom.map_add x y
      map_smul' := fun t m => by
        obtain ⟨s, rfl⟩ := hφ t
        exact e.hom.hom.map_smul s m
      left_inv := fun m => congrArg (fun g => g.hom m) e.hom_inv_id
      right_inv := fun n => congrArg (fun g => g.hom n) e.inv_hom_id }⟩

/-- **The cohomology modules of `ω^•_{A/R} ⊗_A^L A'` and of `ω^•_{A'/R'}` are isomorphic.**  Let
`R` be Noetherian, `R → A` flat of finite type presented by `p`, and `R → R'` arbitrary, with
`A' = R' ⊗_R A`.  For every left-derived model of extension of scalars along `A → A'` and every
degree `i`, the `i`-th cohomology modules of `ω^•_{A/R} ⊗_A^L A'` and of `ω^•_{A'/R'}` are
isomorphic as `A'`-modules.

The two complexes are isomorphic after restriction to `D(P')`
(`Dualizing.nonempty_restrictScalars_derivedBaseChange_relativeDualizing_iso`), so their
cohomology modules are isomorphic over `P'`, hence over `A'` as `P' → A'` is surjective. -/
theorem nonempty_homology_iso_relativeDualizing_baseChange [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (TensorProduct R R' A)) i).obj
        (bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (TensorProduct R R' A)) i).obj
        ((p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')))) := by
  obtain ⟨σ⟩ := nonempty_restrictScalars_derivedBaseChange_relativeDualizing_iso p hflat bcT cmpT
    ldT
  let U := ModuleCat.restrictScalars.{u} (p.baseChange (R' := R')).toRingHom
  let c := StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U i
  exact nonempty_iso_of_restrictScalars_iso_of_surjective _ (p.baseChange (R' := R')).surjective
    ((c.app _).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (p.baseChange (R' := R')).Poly) i).mapIso σ ≪≫
      c.app _)

/-- `Dualizing.nonempty_homology_iso_relativeDualizing_baseChange` at the canonical model
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of extension of scalars
along `A → A' = R' ⊗_R A`. -/
theorem nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (TensorProduct R R' A)) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).functor.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (TensorProduct R R' A)) i).obj
        ((p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')))) :=
  nonempty_homology_iso_relativeDualizing_baseChange p hflat _ _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom).isLeftDerived
    i

end Dualizing

end
