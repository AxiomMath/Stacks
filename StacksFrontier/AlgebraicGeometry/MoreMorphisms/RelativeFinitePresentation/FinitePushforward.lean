module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Finite
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine

/-!
# Relative finite presentation and finite pushforward

Let `π : X ⟶ Y` be a finite morphism of schemes locally of finite type over a base scheme `S`.
Pushforward along `π` neither creates nor destroys finite presentation relative to `S`: a
quasi-coherent `𝒪_X`-module is finitely presented relative to `S` exactly when `π_* ℱ` is.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_pushforward_iff` is the equivalence above.

## Implementation notes

The two structure morphisms to the base are recorded separately, together with the equation
saying that `π` is a morphism over the base, so that the statement applies to a commuting
triangle as it stands.

The proof is the scheme-theoretic translation of the algebraic statement
`Module.finitePresentationRel_iff_of_finite`: over an affine open `V` of the base and an affine
open `U` of `Y` lying over it, the ring `Γ(X, π⁻¹ U)` is a finite `Γ(Y, U)`-algebra and both are
of finite type over `Γ(S, V)`, so relative finite presentation of `Γ(ℱ, π⁻¹ U)` does not depend
on which of the two rings it is read over.

## References

* [Stacks Project, Tag 09T9](https://stacks.math.columbia.edu/tag/09T9)
* [Stacks Project, Tag 05H0](https://stacks.math.columbia.edu/tag/05H0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Over an affine open `V` of the base and an affine open `U` of `Y` lying over it, the module
of sections of `M` on `π⁻¹ U` is finitely presented relative to `Γ(S, V)` as a module over
`Γ(Y, U)` if and only if it is as a module over `Γ(X, π⁻¹ U)`. -/
lemma finitePresentationRel_preimage_iff
    {X Y S : Scheme.{u}} (π : X ⟶ Y) (g : Y ⟶ S) [IsFinite π] [LocallyOfFiniteType g]
    (M : X.Modules) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : S.Opens) (hV : IsAffineOpen V) (hUV : U ≤ g ⁻¹ᵁ V) :
    (letI : Algebra Γ(S, V) Γ(Y, U) := (g.appLE V U hUV).hom.toAlgebra
     letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
     letI : Module Γ(Y, U) Γ(M, π ⁻¹ᵁ U) :=
       Module.compHom Γ(M, π ⁻¹ᵁ U) (algebraMap Γ(Y, U) Γ(X, π ⁻¹ᵁ U))
     Module.FinitePresentationRel Γ(S, V) Γ(Y, U) Γ(M, π ⁻¹ᵁ U)) ↔
    (letI : Algebra _ _ := ((π ≫ g).appLE V (π ⁻¹ᵁ U) (π.preimage_mono hUV)).hom.toAlgebra
     Module.FinitePresentationRel Γ(S, V) Γ(X, π ⁻¹ᵁ U) Γ(M, π ⁻¹ᵁ U)) := by
  let : Algebra Γ(S, V) Γ(Y, U) := (g.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Algebra _ _ := ((π ≫ g).appLE V (π ⁻¹ᵁ U) (π.preimage_mono hUV)).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE])
  let : Module Γ(Y, U) Γ(M, π ⁻¹ᵁ U) :=
    Module.compHom Γ(M, π ⁻¹ᵁ U) (algebraMap Γ(Y, U) Γ(X, π ⁻¹ᵁ U))
  have : IsScalarTower Γ(Y, U) Γ(X, π ⁻¹ᵁ U) Γ(M, π ⁻¹ᵁ U) := .of_compHom _ _ _
  have : Algebra.FiniteType Γ(S, V) Γ(Y, U) := g.finiteType_appLE hV hU hUV
  have : Algebra.FiniteType Γ(S, V) Γ(X, π ⁻¹ᵁ U) :=
    (π ≫ g).finiteType_appLE hV (hU.preimage π) _
  have : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := π.finite_app U hU
  exact Module.finitePresentationRel_iff_of_finite _ _ _ _

/-- **Stacks Project, Tag 09T9.** A quasi-coherent module on the source of a finite morphism
between schemes locally of finite type over a base is finitely presented relative to that base
if and only if its pushforward is. -/
@[stacks 09T9]
theorem isFinitelyPresentedRelative_pushforward_iff
    {X Y S : Scheme.{u}} (π : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (hπ : π ≫ g = f) [IsFinite π] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (M : X.Modules) [M.IsQuasicoherent] :
    IsFinitelyPresentedRelative g ((Scheme.Modules.pushforward π).obj M) ↔
      IsFinitelyPresentedRelative f M := by
  subst f
  constructor
  · rintro ⟨J, V, hVcover, hVaff, hN⟩
    refine ⟨J, V, hVcover, hVaff, fun j ↦ ?_⟩
    obtain ⟨I, U, hU, hUaff, hNU⟩ := hN j
    refine ⟨I, fun i ↦ π ⁻¹ᵁ (U i), ?_, fun i ↦ (hUaff i).preimage π, fun i ↦ ?_⟩
    · rw [← π.preimage_iSup U, hU]
      rfl
    · exact (finitePresentationRel_preimage_iff π g M (U i) (hUaff i)
        (V j) (hVaff j) ((le_iSup U i).trans hU.le)).mp (hNU i)
  · intro hM
    have : ((Scheme.Modules.pushforward π).obj M).IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff π
        ((Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardModules
          π.base X.ringCatSheaf).obj M)).2
          (Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent π M
            inferInstance)
    exact (isFinitelyPresentedRelative_iff_affine g _).2 fun U hU V hV hUV ↦
      (finitePresentationRel_preimage_iff π g M U hU V hV hUV).mpr
        ((isFinitelyPresentedRelative_iff_affine (π ≫ g) M).mp hM (π ⁻¹ᵁ U) (hU.preimage π) V hV
          (π.preimage_mono hUV))

end AlgebraicGeometry

end
