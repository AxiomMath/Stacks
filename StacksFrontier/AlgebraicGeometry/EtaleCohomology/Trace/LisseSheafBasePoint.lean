module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence

/-!
# The lisse sheaf of a finite continuous module at two base points

Let `X` be a connected scheme with geometric points `x̄`, `x̄'` and `t : F_x̄ ≅ F_x̄'` an
isomorphism of fibre functors (Tag 0BND (2)), inducing `φ_t : π₁(X, x̄') → π₁(X, x̄)`. For a finite
ring `Λ`, the equivalence of Tag 0DV5 (3) at `x̄`, followed by restriction along `φ_t`, is the one
at `x̄'` (`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso`): this is
the base-point change of the abelian equivalence of Tag 0DV5 (2)
(`Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`) read on the
scalar operations, exactly as Tag 0DV6 for modules is read off Tag 0DV6 for abelian sheaves.
Conjugating, the lisse sheaf `ℱ_P` of a finite continuous `π₁(X, x̄)`-module `P` built at `x̄` is
the lisse sheaf of `P` restricted along `φ_t` built at `x̄'`
(`Stacks.EtaleCohomology.nonempty_lisseSheaf_basePointIso`).

This lets sheaves defined once, at one base point (the sheaves `Qⱼ` of the model of Laumon's
Fourier family, [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), be compared with lisse
sheaves at the image of an arbitrary geometric point.

## Main results

* `AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso`.
* `Stacks.EtaleCohomology.nonempty_lisseSheaf_basePointIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf Stacks.GroupCohomology
  AlgebraicGeometry

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **Tag 0DV5 (3) at two base points**: the equivalence at `x̄` followed by restriction along
`π₁(X, x̄') → π₁(X, x̄)` is the equivalence at `x̄'`. -/
theorem nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    Nonempty ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor ⋙
        finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupBasePointHom t) ≅
      𝟭 _ ⋙ (finiteTypeLocallyConstantModuleSheafEquivalence B X x' Λ).functor) := by
  have α := finiteLocallyConstantAbelianSheafEquivalenceBasePointIso B X t
  let S := (finiteTypeLocallyConstantModuleSheafBridge B X Λ).symm.trans
    (finiteLocallyConstantModuleSheafScalarActionEquivalence (SmallEtale.topology B X.1 X.2) Λ)
  have h₂ := (Equivalence.conjugateSquare
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x))
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x'))
    (eqToIso (finiteTypeContinuousModuleToScalarAction_res Λ
      (etaleFundamentalGroupBasePointHom t)))).symm
  exact ⟨scalarActionTransportSquare Λ S S
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x)).symm
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x')).symm
    (Iso.refl _) h₂ α⟩

/-- **The lisse sheaf at two base points**: `ℱ_P` built at `x̄` is `ℱ_{P|φ_t}` built at `x̄'`,
naturally in the finite continuous `π₁(X, x̄)`-module `P`. -/
theorem nonempty_lisseSheaf_basePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    Nonempty (lisseSheaf B X x Λ ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupBasePointHom t) ⋙
        lisseSheaf B X x' Λ) := by
  obtain ⟨α⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso B X Λ t
  set E := finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ
  set E' := finiteTypeLocallyConstantModuleSheafEquivalence B X x' Λ
  set res := finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupBasePointHom t)
  -- `E⁻¹ ≅ E⁻¹ ⋙ E' ⋙ E'⁻¹ ≅ E⁻¹ ⋙ E ⋙ res ⋙ E'⁻¹ ≅ res ⋙ E'⁻¹`
  have β : E.inverse ≅ res ⋙ E'.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E'.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerLeft _ α.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _) _
  exact ⟨Functor.isoWhiskerRight β (ObjectProperty.ι _) ≪≫ Functor.associator _ _ _⟩

end Stacks.EtaleCohomology

end
