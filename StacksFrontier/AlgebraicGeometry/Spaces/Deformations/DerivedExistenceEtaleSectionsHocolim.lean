module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTensorSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatPullbackSectionsHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitIsZero

/-!
# Derived sections over an étale space in Situation 0DIK

In Situation [Stacks, Tag 0DIK] let `j : U ⟶ X` be étale with `U` quasi-compact and
quasi-separated. The derived sections `RΓ_A(U, M|_U)` of an object `M` of `D_QCoh(𝒪_X)` vanish
as soon as every `RΓ_A(X, E ⊗^L M)` with `E` perfect does, and the canonical map
`RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` is an isomorphism.

## Main results

* `DerivedExistenceSystem.isZero_etaleSections_of_forall_isPerfect`: for `M ∈ D_QCoh(𝒪_X)`
  with `RΓ_A(X, E ⊗^L M) = 0` for every perfect `E`, also `RΓ_A(U, M|_U) = 0`.
* `DerivedExistenceSystem.isIso_etaleSectionsBaseChangeMap_of_isIso`: the canonical map
  `RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` is invertible given that every
  `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` with `E` perfect is invertible.
* `DerivedExistenceSystem.isIso_etaleSectionsBaseChangeMap`: for `K = DQ_X(R lim Kₙ)` and
  `j : U ⟶ X` étale with `U` quasi-compact and quasi-separated, the canonical map
  `RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` is an isomorphism in `D(Aₙ)`.

## References

* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace DerivedExistenceSystem

variable {D : DerivedExistenceSystem.{u}}
  {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} {j : U ⟶ D.X.left}

/-- For `M ∈ D_QCoh(𝒪_X)` and `j : U ⟶ X` étale with `U` quasi-compact and quasi-separated,
`RΓ_A(U, M|_U)` vanishes when every `RΓ_A(X, E ⊗^L M)` with `E` perfect does. -/
theorem isZero_etaleSections_of_forall_isPerfect
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1)
    (M : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)))
    (hM : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left M)
    (h : ∀ E : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left)),
      (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
        D.X.left.2).IsPerfect E →
      IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).obj
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase D.X.hom).obj
            (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
              D.X.left).obj E).obj M)))) :
    IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            M))) := by
  have toBase_eq : ∀ {V} (f : V ⟶ _), f =
      DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase V := fun _ ↦
    ObjectProperty.hom_ext _
      ((isTerminal_yoneda_obj_base D.B (limitBase D.system) D.containsLimitBase).hom_ext _ _)
  have hU : j ≫ D.X.hom = _ := toBase_eq _
  have hXfp := D.finitePresentation
  rw [toBase_eq D.X.hom] at hXfp h
  have hUfp := D.isFinitePresentation_structure_of_isEtale hj hUqc hUqs
  rw [hU] at hUfp ⊢
  obtain ⟨E, hE, ι, hι⟩ := exists_isHomotopyColimitCocone_derivedSections_tensor_of_isFlat
    D.B (A := ((limit D.system : CommRingCat) : Type u)) D.containsLimitBase j hXfp hUfp
    (isFlat_of_isEtale D.B (limitBase D.system) D.containsLimitBase hj)
  exact (hι M hM).isHomotopyColimit.isZero_of_forall_isZero fun m ↦ h _ (hE m)

/-- If for every perfect `E` on `X` the map `RΓ_{Aₙ}(Xₙ, Lpₙ^*E ⊗^L τₙ)` is invertible, then
`RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` is an isomorphism, for `j : U ⟶ X` étale with `U`
quasi-compact and quasi-separated. -/
theorem isIso_etaleSectionsBaseChangeMap_of_isIso
    (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory)
    (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ)
    (h0DIM : ∀ E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E →
      IsIso ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) ⋙
        representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase (D.stage n)).obj
          ((D.stageDerivedPullback n).obj E)).map (D.coheratorLimitPullbackMap DQ adj n)))) :
    IsIso (D.etaleSectionsBaseChangeMap j DQ adj n) :=
  D.isIso_etaleSectionsBaseChangeMap_of_forall DQ adj hj hUqc hUqs n
    (isZero_etaleSections_of_forall_isPerfect hj hUqc hUqs) h0DIM

variable (D) (j) in
/-- In Situation 0DIK let `K = DQ_X(R lim Kₙ)` be the object of [Stacks, Tag 0DIL]
(`AlgebraicGeometry.Space.DerivedExistenceSystem.quasicoherentLimit`, for the coherator `DQ_X`
right adjoint to `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`). For every étale `j : U ⟶ X` with `U`
quasi-compact and quasi-separated and every `n`, the canonical map
`RΓ(U, K) ⊗^L_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` in `D(Aₙ)`, with `Uₙ = U ×_X Xₙ` (the base change map of `RΓ`
along `Spec Aₙ ⟶ Spec A`, then `RΓ(Uₙ, -)` of `τₙ|_{Uₙ}`, with `τₙ : Lpₙ^*K ⟶ Kₙ` adjoint to the
projection), is an isomorphism. -/
@[stacks 0DIP "for U → X étale with U qcqs, RΓ(U, K) ⊗^L_A A_n → RΓ(U_n, K_n) is an isomorphism \
  in D(A_n), U_n = U ×_X X_n; nothing is granted or assumed"]
theorem isIso_etaleSectionsBaseChangeMap
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) (n : ℕ) :
    IsIso (D.etaleSectionsBaseChangeMap j D.coherator D.coheratorAdjunction n) :=
  isIso_etaleSectionsBaseChangeMap_of_isIso D.coherator D.coheratorAdjunction hj hUqc hUqs n
    (D.isIso_stageSections_map_tensor_coheratorLimitPullbackMap D.coherator
      D.coheratorAdjunction n)

end DerivedExistenceSystem

end AlgebraicGeometry.Space
