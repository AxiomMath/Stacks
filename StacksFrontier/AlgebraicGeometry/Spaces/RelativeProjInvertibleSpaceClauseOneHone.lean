module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaChartMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointPullbackHomApp

/-!
# Clause (1) of Stacks 0D2Z at the scheme points of `U(ψ)`

Clause (1) of [Stacks, Tag 0D2Z] on the algebraic space `U(ψ)` is descended from the identity
`w^*(ψ_P leg) ≫ χ_w = w^*(ψ leg)` at the scheme points `w : W ⟶ U(ψ)` (the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`).  This file proves the
pieces of the target square of that identity which concern the restriction `x^*ψ` of `ψ` to a
scheme point (`AlgebraicGeometry.Space.pointPsi`), read through the identifications of the
restricted modules with the modules attached to their Zariski readings.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_psi_app_comp_pointTargetIso_hom`: the inverse image
  of `ψ_n` along a scheme point, through the identifications of its source and target with the
  attached modules, is the module attached to the restriction of `ψ`.
* `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso_hom_comp_map_pullbackPointHom_app`: the
  comparison `x^*(f^*𝒜) ≅ (f ∘ x)^*𝒜` of restricted algebras, on the attached modules, is the
  composition comparison of Stacks 03LU.
* `AlgebraicGeometry.Space.compIso_hom_app_comp_map_pointPsi_app`: the target square at a scheme
  point, on the restricted algebras: the composition comparison followed by the module attached
  to `x^*ψ` is the inverse image of `ψ_n` followed by the identification of its target.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

section PsiPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)).obj A)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L))
  (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ)

/-- The module attached to a composite of two morphisms of quasi-coherent modules, the second
one the identification `pointLaurentReadingIso`, on underlying morphisms. -/
theorem map_zariskiReadingQcohMap_hom_comp_map_pointLaurentReadingIso_hom
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite)
    (hN' : ((etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        T x).piece n).IsQuasicoherentOnSite) :
    ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (zariskiReadingQcohMap T hN hN' ((modulePullback B S hS (pointHom x)).map (ψ.app n)))).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (pointLaurentReadingIso L T x n).hom).hom =
    ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (ObjectProperty.homMk ((pointAlgebraHom ψ T x).app n ≫
          (pointLaurentHom B S hS L T x).app n) :
          zariskiReadingQcoh T _ hN ⟶ pointLaurentPieceQcoh L T x n)).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp]
  rfl

/-- **The restriction of `ψ` to a scheme point, through the identifications with the attached
modules**: for a scheme point `x : T ⟶ X`, the inverse image along `x` of `ψ_n`, followed by the
identification `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a`, is the identification
`x^*((f^*𝒜)_n) ≅ ((x^*(f^*𝒜))_n)^a` followed by the module attached to the restriction
`AlgebraicGeometry.Space.pointAlgebraHom` of `ψ` and the identification
`AlgebraicGeometry.Space.pointLaurentHom` of the restricted Laurent algebra. -/
theorem modulePullback_map_psi_app_comp_pointTargetIso_hom
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite) :
    (modulePullback B S hS (pointHom x)).map (ψ.app n) ≫ (pointTargetIso L T x n).hom =
      (zariskiReadingQuasicoherentIso T _ hN).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (ObjectProperty.homMk ((pointAlgebraHom ψ T x).app n ≫
            (pointLaurentHom B S hS L T x).app n) :
            zariskiReadingQcoh T _ hN ⟶ pointLaurentPieceQcoh L T x n)).hom := by
  have hN' := isQuasicoherentOnSite_etalePointAlgebra_piece
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
    (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x n
  have h1 := zariskiReadingQuasicoherentIso_hom_naturality T hN hN'
    ((modulePullback B S hS (pointHom x)).map (ψ.app n))
  exact (congrArg (fun k => (modulePullback B S hS (pointHom x)).map (ψ.app n) ≫ k)
    (pointTargetIso_hom L T x n)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (pointLaurentReadingIso L T x n).hom).hom) h1.symm).trans ((Category.assoc _ _ _).trans
          (congrArg (fun k => (zariskiReadingQuasicoherentIso T _ hN).hom ≫ k)
            (map_zariskiReadingQcohMap_hom_comp_map_pointLaurentReadingIso_hom f A L ψ T x n hN
              hN')))))

/-- The comparison of the restrictions of `f^*𝒜` and `𝒜` along the identity of `f^*𝒜`, before
the Zariski reading, is `AlgebraicGeometry.Space.pointPullbackHom`. -/
theorem pullbackEtalePointHom_refl :
    pullbackEtalePointHom f A (Iso.refl _) T x = pointPullbackHom f A T x :=
  (congrArg (· ≫ pointPullbackHom f A T x) ((gradedPull
    (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS (pointHom x))).map_id _)).trans (Category.id_comp _)

/-- **The comparison `x^*(f^*𝒜) ≅ (f ∘ x)^*𝒜` of restricted algebras, carried to the attached
modules, is the composition comparison of Stacks 03LU**: the identification
`x^*((f^*𝒜)_n) ≅ ((x^*(f^*𝒜))_n)^a` followed by the module attached to
`AlgebraicGeometry.Space.pullbackPointHom` in degree `n` is the comparison
`x^*(f^*𝒜_n) ≅ (x ≫ f)^*𝒜_n`, the transport along `x ≫ f = f ∘ x` and the identification
`(f ∘ x)^*𝒜_n ≅ (((f ∘ x)^*𝒜)_n)^a`. -/
theorem zariskiReadingQuasicoherentIso_hom_comp_map_pullbackPointHom_app
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite) :
    (zariskiReadingQuasicoherentIso T _ hN).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (ObjectProperty.homMk ((pullbackPointHom f A (Iso.refl _) T x).app n) :
            zariskiReadingQcoh T _ hN ⟶ zariskiReadingQcoh T _
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n))).hom =
      (modulePullbackCompIso B S hS (pointHom x) f).hom.app (A.piece n) ≫
        pullbackTransport (A.piece n) (rfl : pointHom x ≫ f = pointHom (x ≫ f.hom)) ≫
        (zariskiReadingQuasicoherentIso T _
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)).hom := by
  have h1 := zariskiReadingQuasicoherentIso_hom_naturality T hN
    (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)
    ((pullbackEtalePointHom f A (Iso.refl _) T x).app n)
  have h2 : (pullbackEtalePointHom f A (Iso.refl _) T x).app n =
      (modulePullbackCompIso B S hS (pointHom x) f).hom.app (A.piece n) ≫
        pullbackTransport (A.piece n) (rfl : pointHom x ≫ f = pointHom (x ≫ f.hom)) :=
    (congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n)
      (pullbackEtalePointHom_refl f A T x)).trans (pointPullbackHom_app_eq f A T x n)
  exact h1.trans ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))

/-- The modules attached to the comparison `pullbackPointHom` and to `pointPsi`, composed: the
module attached to the restriction of `ψ` followed by `pointLaurentHom`. -/
theorem map_homMk_pullbackPointHom_app_comp_map_homMk_pointPsi_app
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite) :
    ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (ObjectProperty.homMk ((pullbackPointHom f A (Iso.refl _) T x).app n) :
          zariskiReadingQcoh T _ hN ⟶ zariskiReadingQcoh T _
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n))).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (ObjectProperty.homMk ((pointPsi f A L ψ T x).app n) :
          zariskiReadingQcoh T _ (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)
            ⟶ pointLaurentPieceQcoh L T x n)).hom =
    ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (ObjectProperty.homMk ((pointAlgebraHom ψ T x).app n ≫
          (pointLaurentHom B S hS L T x).app n) :
          zariskiReadingQcoh T _ hN ⟶ pointLaurentPieceQcoh L T x n)).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp]
  exact congrArg (fun k => ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map k).hom)
    (ObjectProperty.hom_ext _ ((congrArg (_ ≫ ·) (pointPsi_app f A L ψ T x n)).trans
      (@IsIso.hom_inv_id_assoc _ _ _ _ _ (isIso_pullbackPointHom_app f A (Iso.refl _) T x n) _
        _)))

/-- **The target square of clause (1) of Stacks 0D2Z at a scheme point, on the restricted
algebras**: the comparison `x^*(f^*𝒜_n) ≅ (x ≫ f)^*𝒜_n` of Stacks 03LU, the transport along
`x ≫ f = f ∘ x` and the identification `(f ∘ x)^*𝒜_n ≅ (((f ∘ x)^*𝒜)_n)^a`, followed by the module
attached to the restriction `x^*ψ` of `ψ` in degree `n` (`AlgebraicGeometry.Space.pointPsi`), is
the inverse image along `x` of `ψ_n` followed by the identification
`x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a`. -/
theorem compIso_hom_app_comp_map_pointPsi_app
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite) :
    (modulePullbackCompIso B S hS (pointHom x) f).hom.app (A.piece n) ≫
        pullbackTransport (A.piece n) (rfl : pointHom x ≫ f = pointHom (x ≫ f.hom)) ≫
        (zariskiReadingQuasicoherentIso T _
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (ObjectProperty.homMk ((pointPsi f A L ψ T x).app n) :
            zariskiReadingQcoh T _
                (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)
              ⟶ pointLaurentPieceQcoh L T x n)).hom =
      (modulePullback B S hS (pointHom x)).map (ψ.app n) ≫ (pointTargetIso L T x n).hom := by
  have hZ := zariskiReadingQuasicoherentIso_hom_comp_map_pullbackPointHom_app f A T x n hA hN
  have hP := map_homMk_pullbackPointHom_app_comp_map_homMk_pointPsi_app f A L ψ T x n hA hN
  have hT := modulePullback_map_psi_app_comp_pointTargetIso_hom f A L ψ T x n hN
  exact ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm).trans
    ((congrArg (· ≫ _) (hZ.trans (Category.assoc _ _ _).symm).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hP).trans hT.symm)))

end PsiPoint

end AlgebraicGeometry.Space

end
