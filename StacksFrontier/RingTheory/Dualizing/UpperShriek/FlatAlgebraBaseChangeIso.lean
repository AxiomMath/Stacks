module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChangeIso

/-!
# Upper shriek of a flat finite-type homomorphism commutes with base change

Let `R → R'` be a homomorphism of Noetherian rings, let `φ : R → A` be flat of finite type and
let `φ' : R' → A' = R' ⊗_R A` be its base change.  Then `φ^!(K) ⊗_A^L A' ≅ (φ')^!(K ⊗_R^L R')`,
naturally in `K` in `D(R)`.

## Main results

* `Dualizing.nonempty_iso_of_iso_derivedTensor_of_obj_iso` — two functors `D(R) ⥤ D(B)` that are
  each isomorphic to a derived tensor product over `R` with a complex of `B`-modules are
  isomorphic as soon as their values at `R` are.
* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_flat_of_obj_iso` —
  the reduction of [stacks 0BZS] to its value at `R`, which is [stacks 0BZV] case (2).
* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_flat` — the
  isomorphism of functors of [stacks 0BZS], at every module universe.

## Implementation notes

The registered statement is the source's own deduction: 0BZS is the special case of [stacks 0BZR]
in which `φ` is flat of finite type, since such a map is perfect over a Noetherian base
([stacks 067J]) and flatness of `A` makes `A` and `R'` Tor independent over `R`.  It is read at
every module universe `max v u`, as [stacks 0BZR] is.

The file also records a second proof, at module universe equal to the ring universe, along the
route of [stacks 0BZU] and [stacks 0BZV].  Since `φ` and `φ'` are perfect, [stacks 0BZU] writes
both sides as derived tensor products: `φ^!(K) ⊗_A^L A' = (K ⊗_R^L ω_{A/R}) ⊗_A^L A'` and
`(φ')^!(K ⊗_R^L R') = (K ⊗_R^L R') ⊗_{R'}^L ω_{A'/R'}`.  By the associativity of iterated derived
change of rings, [stacks 08YU], each is derived tensor product over `R` with a single complex of
`A'`-modules, and such a functor is determined up to isomorphism by its value at `R`; the two
values are `ω_{A/R} ⊗_A^L A'` and `ω_{A'/R'}`, which agree by [stacks 0BZV] case (2).

Upper shriek is read at an arbitrary polynomial presentation of `φ` and an arbitrary one of `φ'`
(their independence being [stacks 0BZJ]), and the two derived extensions of scalars at arbitrary
left-derived models.

## References

* [Stacks Project, Tag 0BZS](https://stacks.math.columbia.edu/tag/0BZS)
* [Stacks Project, Tag 0BZR](https://stacks.math.columbia.edu/tag/0BZR)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing

section TensorFunctor

variable {R B : Type u} [CommRing R] [CommRing B]

/-- A left-derived model of extension of scalars along `g : R → B` is derived tensor product over
`R` with the unit complex of `B`. -/
def derivedExtensionIsoCanonicalTensorUnit (g : R →+* B)
    (bc : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (cmp : DerivedCategory.Q ⋙ bc ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (ld : bc.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} B) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} B) :=
      ModuleCat.liftedModuleMonoidal.{u, u}
    bc ≅ (canonicalDerivedTensorChangeOfRings.{u, u, u} g
      (HomologicalComplex.tensorUnit (ModuleCat.{u} B) (ComplexShape.up ℤ))).F := by
  letI : MonoidalCategoryStruct (ModuleCat.{u} B) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  letI : MonoidalCategory (ModuleCat.{u} B) :=
    ModuleCat.liftedModuleMonoidal.{u, u}
  let F := ModuleCat.extendScalars.{u, u, u} g
  let N := HomologicalComplex.tensorUnit (ModuleCat.{u} B) (ComplexShape.up ℤ)
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} g N
  let eTensor : CochainComplex.tensorRightLarge.{u, u} N ≅
      𝟭 (CochainComplex (ModuleCat.{u} B) ℤ) :=
    trightCochainTensorUnitIso (ModuleCat.{u} B)
  let eDirect : T.directTensor ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) := by
    simpa [T, N, F, CochainComplex.extendScalarsLarge] using
      (T.directTensorComparison ≪≫
        Functor.isoWhiskerLeft (CochainComplex.extendScalarsLarge g) eTensor ≪≫
        Functor.rightUnitor (CochainComplex.extendScalarsLarge g))
  exact Functor.leftDerivedNatIso bc T.F cmp T.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight eDirect DerivedCategory.Q).symm

/-- Derived tensor product over `R` with a complex of `B`-modules transported along an equality of
ring maps `R → B`. -/
def canonicalDerivedTensorCongr {g₁ g₂ : R →+* B} (h : g₁ = g₂)
    (X : CochainComplex (ModuleCat.{u} B) ℤ) :
    (canonicalDerivedTensorChangeOfRings.{u, u, u} g₁ X).F ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, u} g₂ X).F := by
  subst h
  exact Iso.refl _

/-- **A derived tensor functor is determined by its value at the base.**  Let `F` and `G` be
functors `D(R) ⥤ D(B)` each isomorphic to derived tensor product over `R` with a complex of
`B`-modules.  If `F(R) ≅ G(R)`, then `F ≅ G`: the value at `R` of `- ⊗_R^L X` is `X`, and derived
tensor product with `X` depends only on the class of `X` in `D(B)`. -/
theorem nonempty_iso_of_iso_derivedTensor_of_obj_iso (g : R →+* B)
    (X Y : CochainComplex (ModuleCat.{u} B) ℤ)
    {F G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (eF : F ≅ (canonicalDerivedTensorChangeOfRings.{u, u, u} g X).F)
    (eG : G ≅ (canonicalDerivedTensorChangeOfRings.{u, u, u} g Y).F)
    (e : F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      G.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :
    Nonempty (F ≅ G) := by
  let : MonoidalCategoryStruct (ModuleCat.{u} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} R) :=
    ModuleCat.liftedModuleMonoidal.{u, u}
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let R₀ := S.obj (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))
  let eU : R₀ ≅ S.obj (ModuleCat.of R R) :=
    S.mapIso (ULift.moduleEquiv.{u, u, u} (R := R) (M := R)).toModuleIso
  let Q := DerivedCategory.Q (C := ModuleCat.{u} B)
  let eQ : Q.obj X ≅ Q.obj Y :=
    (derivedTensorUnitEvaluationIso.{u, u} g X).symm ≪≫ (eF.app R₀).symm ≪≫ F.mapIso eU ≪≫ e ≪≫
      G.mapIso eU.symm ≪≫ eG.app R₀ ≪≫ derivedTensorUnitEvaluationIso.{u, u} g Y
  let eQh := DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)
  obtain ⟨eT⟩ := derivedTensorRepresentative_congr.{u, u} g X Y
    (eQh.app X ≪≫ eQ ≪≫ (eQh.app Y).symm)
  exact ⟨eF ≪≫ eT ≪≫ eG.symm⟩

end TensorFunctor

section BaseChange

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

/-- The base-changed presentation `Dualizing.PolynomialPresentation.baseChange`, read as a
presentation of the structure map `R' → R' ⊗_R A`; the two ring maps are equal. -/
private def PolynomialPresentation.baseChangeAlgebraMap
    (p : PolynomialPresentation (algebraMap R A)) :
    PolynomialPresentation (algebraMap R' (TensorProduct R R' A)) where
  variableCount := (p.baseChange (R' := R')).variableCount
  toRingHom := (p.baseChange (R' := R')).toRingHom
  commutes := by
    rw [(p.baseChange (R' := R')).commutes]
    ext r
    simp
  surjective := (p.baseChange (R' := R')).surjective

/-- **The reduction of [stacks 0BZS] to [stacks 0BZV] case (2).**  Let `R` and `R'` be
Noetherian and let `φ : R → A` be flat with polynomial presentation `p`; let `p'` be any
polynomial presentation of `φ' : R' → A' = R' ⊗_R A`.  Given an isomorphism
`ω_{A/R} ⊗_A^L A' ≅ ω_{A'/R'}`, the functors `φ^!(-) ⊗_A^L A'` and `(φ')^!(- ⊗_R^L R')` are
isomorphic.

Both `φ` and `φ'` are flat of finite presentation, hence perfect, so by [stacks 0BZU] both
functors are composites of two derived tensor products, which by [stacks 08YU] are single
derived tensor products over `R` with complexes of `A'`-modules; such a functor is determined by
its value at `R`, and the two values are the two sides of the given isomorphism. -/
theorem PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_flat_of_obj_iso
    [IsNoetherianRing R] [IsNoetherianRing R']
    (hflat : (algebraMap R A).Flat)
    (p : PolynomialPresentation (algebraMap R A))
    (p' : PolynomialPresentation (algebraMap R' (TensorProduct R R' A)))
    (bcR : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (e : bcT.obj (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) :
    Nonempty (p.upperShriekFunctor.{u, 0} ⋙ bcT ≅ bcR ⋙ p'.upperShriekFunctor.{u, 0}) := by
  classical
  let f := algebraMap R A
  let i := algebraMap R R'
  let j := (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom
  let f' := algebraMap R' (TensorProduct R R' A)
  have hcomm : j.comp f = f'.comp i := by
    ext r
    simp [j, f, f', i, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have hflat' : f'.Flat := RingHom.flat_algebraMap_iff.mpr (Module.Flat.baseChange R R' A)
  let T := p.tensorFormulaOfPerfect.{u, 0} (p.isPerfectModule_of_flat hflat)
  let T' := p'.tensorFormulaOfPerfect.{u, 0} (p'.isPerfectModule_of_flat hflat')
  let : MonoidalCategoryStruct (ModuleCat.{u} (TensorProduct R R' A)) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} (TensorProduct R R' A)) :=
    ModuleCat.liftedModuleMonoidal.{u, u}
  let : MonoidalCategoryStruct (ModuleCat.{u} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} R') :=
    ModuleCat.liftedModuleMonoidal.{u, u}
  let eF := Functor.isoWhiskerRight T.iso bcT ≪≫
    Functor.isoWhiskerLeft _ (derivedExtensionIsoCanonicalTensorUnit j bcT cmpT ldT) ≪≫
    IteratedChangeOfRings.doubleBaseChangeIso.{u, u, u, 0} f j T.factor
      (HomologicalComplex.tensorUnit (ModuleCat.{u} (TensorProduct R R' A))
        (ComplexShape.up ℤ)) ≪≫
    canonicalDerivedTensorCongr hcomm _
  let eG := Functor.isoWhiskerRight (derivedExtensionIsoCanonicalTensorUnit i bcR cmpR ldR) _ ≪≫
    Functor.isoWhiskerLeft _ T'.iso ≪≫
    IteratedChangeOfRings.doubleBaseChangeIso.{u, u, u, 0} i f'
      (HomologicalComplex.tensorUnit (ModuleCat.{u} R') (ComplexShape.up ℤ)) T'.factor
  let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let R₀' := (DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} i
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} i).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor cmpD W := D.isLeftDerived
  have := ldR
  let eUnit : bcR.obj R₀ ≅ R₀' :=
    (Functor.leftDerivedUnique (LF := bcR) (LF' := D.functor) (α := cmpR) (α'₂ := cmpD)
      (W := W)).app R₀ ≪≫
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsRegularIso i
  obtain ⟨eJ⟩ := nonempty_upperShriekFunctor_iso.{u, 0} f'
    (PolynomialPresentation.baseChangeAlgebraMap (R' := R') p) p'
  exact nonempty_iso_of_iso_derivedTensor_of_obj_iso (f'.comp i) _ _ eF eG
    (e ≪≫ eJ.app R₀' ≪≫ p'.upperShriekFunctor.{u, 0}.mapIso eUnit.symm)

/-- **Stacks 0BZS.**  Let `R` be a Noetherian ring and `R → R'` any homomorphism, let
`φ : R → A` be flat of finite type, presented by `p`, and let `φ' : R' → A' = R' ⊗_R A` be the
induced map, presented by any `p'`.  Then there is an isomorphism of functors `D(R) ⥤ D(A')`
`φ^!(K) ⊗_A^L A' ≅ (φ')^!(K ⊗_R^L R')`, natural in `K`, at every module universe `max v u`; the two
derived tensor products are read at arbitrary left-derived models of extension of scalars.

As in the source this is a special case of [stacks 0BZR],
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_torIndependent`: over a
Noetherian base a flat map of finite type is of finite presentation, hence perfect by
[stacks 067J], and flatness of `A` makes `A` and `R'` Tor independent over `R`.  The source's
Noetherian hypothesis on `R'` is not needed. -/
@[stacks 0BZS]
theorem PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_flat
    [IsNoetherianRing R]
    (hflat : (algebraMap R A).Flat)
    (p : PolynomialPresentation (algebraMap R A))
    (p' : PolynomialPresentation (algebraMap R' (TensorProduct R R' A)))
    (bcR : DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} R'))
    (cmpR : DerivedCategory.Q ⋙ bcR ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldR : bcR.IsLeftDerivedFunctor cmpR
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)))
    (bcT : DerivedCategory (ModuleCat.{max v u} A) ⥤
      DerivedCategory (ModuleCat.{max v u} (TensorProduct R R' A)))
    (cmpT : DerivedCategory.Q ⋙ bcT ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldT : bcT.IsLeftDerivedFunctor cmpT
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) :
    Nonempty (p.upperShriekFunctor.{u, v} ⋙ bcT ≅ bcR ⋙ p'.upperShriekFunctor.{u, v}) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp this
  have := Algebra.Perfect.of_flat_of_finitePresentation R A
  exact p.nonempty_upperShriekFunctor_comp_iso_of_torIndependent.{u, v} p'
    RingTheory.TorIndependence.torIndependent_of_flat_left bcR cmpR ldR bcT cmpT ldT

end BaseChange

end Dualizing

end
