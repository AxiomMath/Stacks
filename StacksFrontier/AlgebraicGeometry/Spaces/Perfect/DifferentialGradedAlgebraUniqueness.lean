module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModuleCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRingOfGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomEquivalence

/-!
# Uniqueness of the differential graded algebra of `D_QCoh` of an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a ring `R`. The proof of
Stacks 09MC constructs, from a K-injective complex `K` representing a perfect generator of
`D_QCoh(𝒪_X)`, the differential graded `R`-algebra `A = Hom_{Comp^dg(𝒪_X)}(K, K)` and the
equivalence `D(A, d) ⥤ D_QCoh(𝒪_X)`, `M ↦ M ⊗_A^𝐋 K`. For a second such complex `L` with
`B = Hom_{Comp^dg(𝒪_X)}(L, L)`, set `Ω = Hom_{Comp^dg(𝒪_X)}(K, L)` and
`Ω' = Hom_{Comp^dg(𝒪_X)}(L, K)`. Then `Ω'` is a differential graded `(A, B)`-bimodule, `Ω` is a
differential graded `(B, A)`-bimodule, and the equivalence `D(A, d) ⥤ D_QCoh(𝒪_X) ⥤ D(B, d)` is
`- ⊗_A^𝐋 Ω'`, with quasi-inverse `- ⊗_B^𝐋 Ω`. This is Stacks 0DK9.

As in `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModuleCategory`, the complexes `K` and
`L` live on the equi-universe model `Y` of the small étale ringed site of `X`, through the
equivalence `D(𝒪_X) ≌ D(𝒪_Y)` of `AlgebraicGeometry.Space.modelEquivalence`, so that the
differential graded algebras and their derived categories have the size of `X`. "Over `R`" is a
ring map `ψ : R ⟶ Γ(X, 𝒪_X)` (that is, a morphism from `X` to `Spec R`); it makes `𝒪_Y` a sheaf of
`R`-algebras, and `A`, `B`, `Ω`, `Ω'` are formed over `R`.

## Main definitions

* `AlgebraicGeometry.Space.modelGlobalSectionsHom`: `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`.
* `AlgebraicGeometry.Space.modelLinear`, `AlgebraicGeometry.Space.modelScalarSections`: the
  `R`-algebra structure of `𝒪_Y`.
* `AlgebraicGeometry.Space.dgaQuasicoherentEquivalence`: the equivalence
  `D(A, d) ≌ D_QCoh(𝒪_X)`, `M ↦ M ⊗_A^𝐋 K`, of the proof of Stacks 09MC.

## Main results

* `AlgebraicGeometry.Space.exists_equivalence_derivedTensor_complexHomBimodule`: **Stacks 0DK9**.

## References

* [Stacks Project, Tag 0DK9](https://stacks.math.columbia.edu/tag/0DK9)
* [Stacks Project, Tag 09MC](https://stacks.math.columbia.edu/tag/09MC)
* [Stacks Project, Tag 09ST](https://stacks.math.columbia.edu/tag/09ST)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The global sections of `𝒪_X` restrict to the model.** A compatible family of sections of
`𝒪_X` over the objects of the small étale site gives one over the objects of the model, the
structure sheaf of the model being the restriction of `𝒪_X` along the model equivalence. -/
def modelGlobalSectionsHom (X : AlgebraicSpaces B S hS) :
    ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) →+*
      ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)) where
  toFun s := ⟨fun U => s.1 (Opposite.op ((smallEtaleModelEquivalence B S hS X.1).functor.obj
      U.unop)), fun f => s.2 ((smallEtaleModelEquivalence B S hS X.1).functor.map f.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (ψ : R →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- The `R`-linear structure of the `𝒪_Y`-modules given by `ψ : R ⟶ Γ(X, 𝒪_X)`. -/
abbrev modelLinear : Linear R (RingedSite.TensorModO.{u, u, u, u, u} (modelSite X)) :=
  RingedSite.linearOfGlobalSections.{u, u, u, u, u} (modelSite X)
    ((modelGlobalSectionsHom X).comp ψ)

/-- Under `AlgebraicGeometry.Space.modelLinear` a scalar multiplies by sections of `𝒪_Y`: `𝒪_Y`
is a sheaf of `R`-algebras. -/
abbrev modelScalarSections :
    letI := modelLinear X ψ
    RingedSite.ScalarSections.{u, u, u, u, u, u} (modelSite X) R :=
  RingedSite.scalarSectionsOfGlobalSections.{u, u, u, u, u} (modelSite X)
    ((modelGlobalSectionsHom X).comp ψ)

variable {X}

/-- A K-injective complex on the model representing a perfect generator of `D_QCoh(𝒪_X)` lies in
the image of `D_QCoh(𝒪_X)`, is compact relative to it (Stacks 09M8), and generates it. -/
theorem isRelativelyCompactGenerator_model (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj))
    (eP : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K) :
        DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))) ≅ P) :
    RingedSite.IsRelativelyCompactGenerator.{u, u, u, u, u} (modelSite X)
      (modelQcohDerived X) K where
  coprod Z c hc hZ := modelQcohDerived_prop_of_isColimit X Z c hc hZ
  mem := (QcohDerived B S hS X).prop_of_iso eP.symm
    (qcohDerived_of_isPerfect_derivedCategoryB X P hP)
  compact := isRelativelyCompactShifts_model hqc hqs K P hP eP
  generates := isZero_of_modelQcohDerived K P hgen eP

variable (X)

/-- **The equivalence `D(A, d) ≌ D_QCoh(𝒪_X)` of the proof of Stacks 09MC**, `M ↦ M ⊗_A^𝐋 K`
for `A = Hom_{Comp^dg(𝒪_X)}(K, K)` over `R`: the equivalence of `D(A, d)` with the image of
`D_QCoh(𝒪_X)` in the model, followed by the identification of that image with `D_QCoh(𝒪_X)`. -/
def dgaQuasicoherentEquivalence
    (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    [(RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K).IsKInjective]
    (hK : RingedSite.IsRelativelyCompactGenerator.{u, u, u, u, u} (modelSite X)
      (modelQcohDerived X) K) :
    letI := modelLinear X ψ
    letI := modelScalarSections X ψ
    DifferentialGradedModule.derivedCategory.{u, u, u}
        (RingedSite.Rep.{u, u, u, u, u, u} (modelSite X) R K).algebra ≌
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  let := modelLinear X ψ
  let := modelScalarSections X ψ
  (hK.equivalence R).trans (quasicoherentDerivedCategoryEquivModel X).symm

/-- Two equivalences with a common target, composed through an equivalence of that target with a
third category, compose to the same functor. -/
def equivalenceTransSymmFunctorIso {C₁ C₂ D D' : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Category* D'] (e₁ : C₁ ≌ D) (e₂ : C₂ ≌ D) (q : D' ≌ D) :
    ((e₁.trans q.symm).trans (e₂.trans q.symm).symm).functor ≅ (e₁.trans e₂.symm).functor :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e₁.functor
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight q.counitIso e₂.inverse ≪≫
      Functor.leftUnitor _)

/-- The derived tensor product with `Hom(L, K)` is isomorphic to the composite of the
equivalences `D(A, d) ≌ D_QCoh(𝒪_X) ≌ D(B, d)` of `dgaQuasicoherentEquivalence`. -/
private theorem nonempty_derivedTensorFunctor_iso_trans_symm_functor
    (K L : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    [(RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K).IsKInjective]
    [(RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) L).IsKInjective]
    (hK : RingedSite.IsRelativelyCompactGenerator.{u, u, u, u, u} (modelSite X)
      (modelQcohDerived X) K)
    (hL : RingedSite.IsRelativelyCompactGenerator.{u, u, u, u, u} (modelSite X)
      (modelQcohDerived X) L) :
    letI := modelLinear X ψ
    letI := modelScalarSections X ψ
    Nonempty (DifferentialGraded.Bimodule.derivedTensorFunctor
        (RingedSite.complexHomBimodule.{u, u, u, u, u} (modelSite X) R K L) ≅
      ((dgaQuasicoherentEquivalence X ψ K hK).trans
        (dgaQuasicoherentEquivalence X ψ L hL).symm).functor) :=
  let := modelLinear X ψ
  let := modelScalarSections X ψ
  ⟨RingedSite.derivedTensorComplexHomBimoduleIsoEquivalence R hL hK ≪≫
    (equivalenceTransSymmFunctorIso (hK.equivalence R) (hL.equivalence R)
      (quasicoherentDerivedCategoryEquivModel X)).symm⟩

/-- **Stacks 0DK9.** *Let `X` be a quasi-compact and quasi-separated algebraic space over a ring
`R`, and let `K` and `L` be K-injective complexes of `𝒪_X`-modules corresponding to perfect
generators of `D_QCoh(𝒪_X)`, with `A = Hom_{Comp^dg(𝒪_X)}(K, K)` and
`B = Hom_{Comp^dg(𝒪_X)}(L, L)`. Set `Ω = Hom_{Comp^dg(𝒪_X)}(K, L)` and
`Ω' = Hom_{Comp^dg(𝒪_X)}(L, K)`. Then `Ω` is a differential graded `B^opp ⊗_R A`-module and `Ω'`
a differential graded `A^opp ⊗_R B`-module, and the equivalence
`D(A, d) ⥤ D_QCoh(𝒪_X) ⥤ D(B, d)` is given by `- ⊗_A^𝐋 Ω'`, and its quasi-inverse by
`- ⊗_B^𝐋 Ω`.*

The bimodules are `AlgebraicGeometry.RingedSite.complexHomBimodule`: `Ω' = Hom(L, K)` is a
`DifferentialGraded.Bimodule A B` (left `A`-action by postcomposition, right `B`-action by
precomposition) and `Ω = Hom(K, L)` a `DifferentialGraded.Bimodule B A`. The equivalences
`D(A, d) ≌ D_QCoh(𝒪_X)` and `D(B, d) ≌ D_QCoh(𝒪_X)` are those of the proof of Stacks 09MC,
`AlgebraicGeometry.Space.dgaQuasicoherentEquivalence`. The conclusion is an equivalence
`D(A, d) ≌ D(B, d)` whose functor is `- ⊗_A^𝐋 Ω'` and whose inverse is `- ⊗_B^𝐋 Ω`, isomorphic
to the composite `D(A, d) ⥤ D_QCoh(𝒪_X) ⥤ D(B, d)` and to its quasi-inverse: the situation of
Stacks 09ST.

`X` is over `R` through the ring map `ψ : R ⟶ Γ(X, 𝒪_X)`; `K` and `L` are complexes on the
equi-universe model of the small étale site of `X`, corresponding through
`AlgebraicGeometry.Space.modelEquivalence` to perfect generators `P` and `Q` of `D_QCoh(𝒪_X)`. -/
@[stacks 0DK9]
theorem exists_equivalence_derivedTensor_complexHomBimodule
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (K L : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    [(RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K).IsKInjective]
    [(RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) L).IsKInjective]
    (P Q : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hQ : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect Q)
    (hgenP : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj))
    (hgenQ : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (Q⟦n⟧ ⟶ E.obj))
    (eP : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K) :
        DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))) ≅ P)
    (eQ : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) L) :
        DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))) ≅ Q) :
    letI := modelLinear X ψ
    letI := modelScalarSections X ψ
    ∃ e : DifferentialGradedModule.derivedCategory.{u, u, u}
          (RingedSite.Rep.{u, u, u, u, u, u} (modelSite X) R K).algebra ≌
        DifferentialGradedModule.derivedCategory.{u, u, u}
          (RingedSite.Rep.{u, u, u, u, u, u} (modelSite X) R L).algebra,
      e.functor = DifferentialGraded.Bimodule.derivedTensorFunctor
          (RingedSite.complexHomBimodule.{u, u, u, u, u} (modelSite X) R K L) ∧
      e.inverse = DifferentialGraded.Bimodule.derivedTensorFunctor
          (RingedSite.complexHomBimodule.{u, u, u, u, u} (modelSite X) R L K) ∧
      Nonempty (e.functor ≅
        ((dgaQuasicoherentEquivalence X ψ K
            (isRelativelyCompactGenerator_model hqc hqs K P hP hgenP eP)).trans
          (dgaQuasicoherentEquivalence X ψ L
            (isRelativelyCompactGenerator_model hqc hqs L Q hQ hgenQ eQ)).symm).functor) ∧
      Nonempty (e.inverse ≅
        ((dgaQuasicoherentEquivalence X ψ K
            (isRelativelyCompactGenerator_model hqc hqs K P hP hgenP eP)).trans
          (dgaQuasicoherentEquivalence X ψ L
            (isRelativelyCompactGenerator_model hqc hqs L Q hQ hgenQ eQ)).symm).inverse) := by
  let := modelLinear X ψ
  let := modelScalarSections X ψ
  have hK := isRelativelyCompactGenerator_model hqc hqs K P hP hgenP eP
  have hL := isRelativelyCompactGenerator_model hqc hqs L Q hQ hgenQ eQ
  obtain ⟨i₁⟩ := nonempty_derivedTensorFunctor_iso_trans_symm_functor X ψ K L hK hL
  obtain ⟨i₂⟩ := nonempty_derivedTensorFunctor_iso_trans_symm_functor X ψ L K hL hK
  exact ⟨(((dgaQuasicoherentEquivalence X ψ K hK).trans
      (dgaQuasicoherentEquivalence X ψ L hL).symm).changeFunctor i₁.symm).changeInverse i₂.symm,
    rfl, rfl, ⟨i₁⟩, ⟨i₂⟩⟩

end AlgebraicGeometry.Space
