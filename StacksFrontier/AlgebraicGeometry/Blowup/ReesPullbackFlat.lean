module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackChart
public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine

/-!
# For a flat morphism the comparison `g^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_Z)ⁿ` is an isomorphism

Let `g : Z ⟶ X` be a flat morphism of schemes and `ℐ` a quasi-coherent sheaf of ideals on `X`.
Over an affine open `V` of `Z` inside the preimage of an affine open `U` of `X`, write
`φ : Γ(X, U) → Γ(Z, V)` for the induced map on functions. The sections of `g^*(ℐⁿ)` over `V` are
`Γ(Z, V) ⊗_{Γ(X, U)} Γ(ℐⁿ, U)`, and on ambient sections the comparison
`Φ : g^*(ℐⁿ) ⟶ (ℐ𝒪_Z)ⁿ` becomes the base change along `φ` of the inclusion
`ℐⁿ(U) ↪ Γ(X, U)`. That base change is injective because `Γ(Z, V)` is flat over `Γ(X, U)`, and
it is surjective for every `g`; so `Φ` is invertible on a basis of opens of `Z`, hence invertible.

In nonnegative degrees this is exactly the datum
`Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange` consumes for the relative
`Proj` situations of `Stacks.Blowup.reesSituation`.

## Main results

* `Stacks.Blowup.reesChartSquare`: on ambient sections over an affine chart the comparison is
  extension of scalars applied to the ambient-section map over `U`.
* `Stacks.Blowup.injective_reesPullbackComparisonLinear`: **flatness is what makes the comparison
  injective on an affine chart.**
* `Stacks.Blowup.isIso_reesGradedPullbackHom_app`: in nonnegative degrees the comparison is an
  isomorphism of sheaves of modules on `Z`.
* `Stacks.Blowup.isIso_reesSituationGradedPullbackHom_app`: the same, in the shape the
  base-change square of a relative `Proj` asks for.

## Implementation notes

The chart identification is an equality of two morphisms out of
`(ModuleCat.extendScalars φ).obj (ModuleCat.of Γ(X, U) Γ(ℐⁿ, U))`, checked on `1 ⊗ a` by
`ModuleCat.ExtendScalars.hom_ext_one_tmul`: `affinePullbackSectionsBaseChangeIso` carries `1 ⊗ a`
to the pullback of `a`, and `reesAmbientLinearMap_reesPullbackComparisonLinear` together with
`ModuleCat.ExtendScalars.objSelfIso_hom_tmul` then give the value `φ(a)` on both sides. The
`ModuleCat.extendScalars` tensor product carries `Module.compHom` rather than the module
structure of `φ.toAlgebra`, and the two spellings are definitionally but not syntactically equal;
every step touching that boundary is therefore an `exact` against a stated equation, never a
rewrite.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open SheafOfModules.GradedAlgebra
open scoped ChangeOfRings

universe u

namespace Stacks.Blowup

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (I : X.IdealSheafData)

/-! ### The chart identification -/

/-- **The comparison over an affine chart is extension of scalars.** Composing the base-change
description of the sections of `g^*(ℐⁿ)` over `V` with `Φ` and with the ambient section of the
result gives the same `Γ(Z, V)`-linear map `Γ(Z, V) ⊗_{Γ(X, U)} Γ(ℐⁿ, U) ⟶ Γ(Z, V)` as extending
the scalars of the ambient-section map `Γ(ℐⁿ, U) ⟶ Γ(X, U)`. -/
lemma reesChartSquare (n : ℤ) [(Stacks.Conormal.reesModule I n).IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    (affinePullbackSectionsBaseChangeIso g (Stacks.Conormal.reesModule I n) hU hV hVU).hom ≫
        ModuleCat.ofHom (reesPullbackComparisonLinear g I n V) ≫
        ModuleCat.ofHom (reesAmbientLinearMap (I.comap g) n V) =
      (ModuleCat.extendScalars (g.appLE U V hVU).hom).map
          (ModuleCat.ofHom (reesAmbientLinearMap I n U)) ≫
        (ModuleCat.ExtendScalars.objSelfIso (g.appLE U V hVU).hom).hom := by
  refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun a => ?_
  have hL := affinePullbackSectionsBaseChangeIso_one_tmul g
    (Stacks.Conormal.reesModule I n) hU hV hVU a
  have hA := reesAmbientLinearMap_reesPullbackComparisonLinear g I n U V hVU a
  have hM := ModuleCat.ExtendScalars.map_tmul (g.appLE U V hVU).hom
    (ModuleCat.ofHom (reesAmbientLinearMap I n U)) (1 : Γ(Z, V)) a
  have hR := ModuleCat.ExtendScalars.objSelfIso_hom_tmul (g.appLE U V hVU).hom
    (1 : Γ(Z, V)) (reesAmbientLinearMap I n U a)
  exact (congrArg (fun z => reesAmbientLinearMap (I.comap g) n V
      (reesPullbackComparisonLinear g I n V z)) hL).trans
    (hA.trans (((_root_.one_mul _).symm.trans hR.symm).trans
      (congrArg (ModuleCat.ExtendScalars.objSelfIso (g.appLE U V hVU).hom).hom hM).symm))

/-! ### Injectivity on an affine chart -/

/-- **Flatness is what makes `Φ` injective on an affine chart.** Through the chart
identification the composite of `Φ` with the ambient section is the base change along
`Γ(X, U) → Γ(Z, V)` of the injective ambient-section map, which is injective because `Γ(Z, V)`
is flat; the base-change description of the sections of `g^*(ℐⁿ)` is bijective, so `Φ` itself is
injective. -/
lemma injective_reesPullbackComparisonLinear (n : ℤ) (hn : 0 ≤ n) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (hflat : (g.appLE U V hVU).hom.Flat) :
    Function.Injective (reesPullbackComparisonLinear g I n V) := by
  have : (Stacks.Conormal.reesModule I n).IsQuasicoherent := reesPiece_isQuasicoherent I n
  have hα : Function.Injective
      ((affinePullbackSectionsBaseChangeIso g (Stacks.Conormal.reesModule I n)
            hU hV hVU).hom ≫
        ModuleCat.ofHom (reesPullbackComparisonLinear g I n V) ≫
        ModuleCat.ofHom (reesAmbientLinearMap (I.comap g) n V)) := by
    rw [reesChartSquare g I n hU hV hVU]
    have h2 := (ConcreteCategory.bijective_of_isIso
      (ModuleCat.ExtendScalars.objSelfIso (g.appLE U V hVU).hom).hom).1
    have h1 := ModuleCat.ExtendScalars.injective_map_of_flat (g.appLE U V hVU).hom hflat
      (ModuleCat.ofHom (reesAmbientLinearMap I n U))
      (injective_reesAmbientLinearMap I n hn U)
    intro x y hxy
    exact h1 (h2 hxy)
  refine Function.Injective.of_comp_right (g := fun x =>
      (affinePullbackSectionsBaseChangeIso g (Stacks.Conormal.reesModule I n)
        hU hV hVU).hom x) ?_ ?_
  · intro x y hxy
    exact hα (congrArg (reesAmbientLinearMap (I.comap g) n V) hxy)
  · exact (ConcreteCategory.bijective_of_isIso
      (affinePullbackSectionsBaseChangeIso g (Stacks.Conormal.reesModule I n) hU hV hVU).hom).2

/-- **`Φ` is bijective on an affine chart** in nonnegative degrees, for a chart on which the map
on functions is flat: injectivity needs that flatness, surjectivity holds for every `g`. -/
lemma bijective_reesPullbackComparisonLinear (n : ℤ) (hn : 0 ≤ n) (U : X.affineOpens)
    (V : Z.affineOpens) (hVU : V.1 ≤ g ⁻¹ᵁ U.1) (hflat : (g.appLE U.1 V.1 hVU).hom.Flat) :
    Function.Bijective (reesPullbackComparisonLinear g I n V.1) :=
  ⟨injective_reesPullbackComparisonLinear g I n hn U.2 V.2 hVU hflat,
    surjective_reesPullbackComparisonLinear g I n hn U V hVU⟩

/-- The component of `Φ` on an affine chart with flat map on functions is invertible. -/
lemma isIso_reesGradedPullbackHom_app_val_app (n : ℤ) (hn : 0 ≤ n) (U : X.affineOpens)
    (V : Z.affineOpens) (hVU : V.1 ≤ g ⁻¹ᵁ U.1) (hflat : (g.appLE U.1 V.1 hVU).hom.Flat) :
    IsIso (((reesGradedPullbackHom g I).app n).val.app (op V.1)) :=
  (ConcreteCategory.isIso_iff_bijective
    (((reesGradedPullbackHom g I).app n).val.app (op V.1))).2
      (bijective_reesPullbackComparisonLinear g I n hn U V hVU hflat)

/-! ### Globalisation -/

/-- **For a flat morphism `g` the comparison `Φ : g^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_Z)ⁿ` is an isomorphism in
every nonnegative degree.** The affine opens of `Z` lying over an affine open of `X` form a basis,
on each of them the map on functions is flat and the component of `Φ` is bijective, and a
morphism of sheaves of modules invertible on a basis is invertible. -/
lemma isIso_reesGradedPullbackHom_app [AlgebraicGeometry.Flat g] (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((reesGradedPullbackHom g I).app n) := by
  refine Stacks.LeibnizDerivation.isIso_of_isIso_app_basis _
    (Stacks.LeibnizDerivation.isBasis_affineOpens_le_preimage g) ?_
  rintro ⟨⟨U, V⟩, hU, hV, hVU⟩
  exact isIso_reesGradedPullbackHom_app_val_app g I n hn ⟨U, hU⟩ ⟨V, hV⟩ hVU
    (AlgebraicGeometry.Flat.flat_appLE g hU hV hVU)

/-- **The invertibility datum of the base-change square of a relative `Proj`**, for the relative
`Proj` situations of `Stacks.Blowup.reesSituation` and a flat morphism `g`. -/
lemma isIso_reesSituationGradedPullbackHom_app [AlgebraicGeometry.Flat g] (m : ℕ) :
    IsIso ((reesSituationGradedPullbackHom g I).app (m : ℤ)) :=
  isIso_reesGradedPullbackHom_app g I (m : ℤ) (Int.natCast_nonneg m)

end Stacks.Blowup

end
