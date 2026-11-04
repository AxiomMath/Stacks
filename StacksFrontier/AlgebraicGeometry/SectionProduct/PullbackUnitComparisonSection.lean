module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitTransport
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection

/-!
# The section produced by the structure-sheaf comparison is the geometric restriction

Let `j : Y' ⟶ Y` be a morphism of schemes and `s` a global section of an `𝒪_Y`-module `M`. The
pullback of `s` as an element of `Γ(M, ⊤)` is `AlgebraicGeometry.pullbackGlobalSections`. Reading
`s` instead as a morphism out of `SheafOfModules.unit`, pulling it back along `j` and composing
with the structure-sheaf comparison `j^*𝒪_Y ≅ 𝒪_{Y'}` gives a global section of `j^*M`. This file
proves that the two agree over the top open.

## Main results

* `Stacks.PullbackUnitComparisonSection.inv_pullbackUnitComparison`: the inverse of
  `Stacks.PullbackTensorCoherence.pullbackUnitComparison` is the inverse of
  `Stacks.PullbackAlgebra.pullbackUnitIso`.
* `Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_eq_pullbackSectionHom` and
  `Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_eq_pullbackUnit`:
  `AlgebraicGeometry.pullbackGlobalSections` is `AlgebraicGeometry.pullbackSectionHom` at the top
  open, and is the unit of the adjunction `j^* ⊣ j_*` there.
* `Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv`: the geometric
  restriction of `s` along `j` is the value over the top open of the global section of `j^*M`
  corresponding to `ε⁻¹ ≫ j^*(s)` under `SheafOfModules.unitHomEquiv`, with `ε` the
  structure-sheaf comparison.
* `Stacks.PullbackUnitComparisonSection.unitHomEquiv_eval_comp` and
  `Stacks.PullbackUnitComparisonSection.inv_pullbackUnitComparison_eval_comp`: the same with a
  morphism `θ` out of `j^*M` composed on.
* `Stacks.PullbackUnitComparisonSection.eval_top_of_sectionHom_eq`: a global section of
  `𝒪_{ℙᵐ}(1)` whose `sectionHom` is the pullback of that of `s` along `g`, followed by `θ`, has
  value over the top open the image under `θ` of the geometric restriction of `s`.
* `Stacks.PullbackUnitComparisonSection.exists_pullback_mulSection_eval_top`: every global
  section `s` of `𝒪_{ℙⁿ}(1)` has a restriction along `(g, θ)` equal to its geometric restriction
  followed by `θ`, and restriction intertwines the two multiplications by `s`.

## Implementation notes

`Stacks.PullbackTensorCoherence.pullbackUnitComparison` is
`Stacks.PullbackAlgebra.unitComparison` with source and target spelled through the unit object
`𝟙_`. Where the surrounding type forces the `SheafOfModules.unit` reading, instance search for
`IsIso (pullbackUnitComparison f)` fails, so statements are given with
`(Stacks.PullbackAlgebra.pullbackUnitIso _).inv`, and the `inv` spelling names the instance
explicitly.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (sectionHom)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape (mulSection)
open Stacks.RelativeVeryAmple (tensorModulesMapIso pullbackTensorModulesIso)

universe u

namespace Stacks.PullbackUnitComparisonSection

/-! ### The two spellings of the structure-sheaf comparison -/

section Ringed

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The inverse of the structure-sheaf comparison read at the unit object `𝟙_` is the inverse of
`Stacks.PullbackAlgebra.pullbackUnitIso`. -/
theorem inv_pullbackUnitComparison :
    inv (pullbackUnitComparison f) = (Stacks.PullbackAlgebra.pullbackUnitIso f).inv :=
  rfl

end Ringed

/-! ### Pulling a global section back -/

section Scheme

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- `AlgebraicGeometry.pullbackGlobalSections` is `AlgebraicGeometry.pullbackSectionHom` at the
top open. -/
theorem pullbackGlobalSections_eq_pullbackSectionHom (M : Y.Modules)
    (h : (⊤ : Y'.Opens) ≤ j ⁻¹ᵁ (⊤ : Y.Opens)) :
    pullbackGlobalSections j M = pullbackSectionHom j M ⊤ ⊤ h :=
  congrArg
    (fun φ => ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤ ≫
      ((Scheme.Modules.pullback j).obj M).presheaf.map φ)
    (Subsingleton.elim _ _)

/-- Pulling a global section back is the unit of the adjunction `j^* ⊣ j_*` at the top open. -/
theorem pullbackGlobalSections_eq_pullbackUnit (M : Y.Modules) (x : Γ(M, ⊤)) :
    pullbackGlobalSections j M x = pullbackUnit j.toLRSHom.toShHom M (op ⊤) x :=
  (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
      (pullbackGlobalSections_eq_pullbackSectionHom j M (by simp))) x).trans
    (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq j M (by simp) x)

/-- Let `s` be a global section of an `𝒪_Y`-module `M`, read as a morphism
`M.unitHomEquiv.symm s` out of `SheafOfModules.unit`. Pulling that morphism back along `j` and
precomposing with the inverse of the structure-sheaf comparison gives a global section of `j^*M`
whose value over the top open is `AlgebraicGeometry.pullbackGlobalSections` of the value of `s`
over the top open. -/
theorem pullbackGlobalSections_unitHomEquiv (M : Y.Modules) (s : M.sections) :
    pullbackGlobalSections j M (s.eval (op ⊤)) =
      (((Scheme.Modules.pullback j).obj M).unitHomEquiv
          ((Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
            (Scheme.Modules.pullback j).map (M.unitHomEquiv.symm s))).eval (op ⊤) :=
  (pullbackGlobalSections_eq_pullbackUnit j M _).trans
    (Stacks.PullbackAlgebra.transportSection_val_top j.toLRSHom.toShHom M s).symm

/-- `Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv` with a morphism
`θ : j^*M ⟶ N` composed on. -/
theorem unitHomEquiv_eval_comp (M : Y.Modules) (N : Y'.Modules) (s : M.sections)
    (θ : (Scheme.Modules.pullback j).obj M ⟶ N) :
    (N.unitHomEquiv ((Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
          (Scheme.Modules.pullback j).map (M.unitHomEquiv.symm s) ≫ θ)).eval (op ⊤) =
      θ.app ⊤ (pullbackGlobalSections j M (s.eval (op ⊤))) :=
  congrArg (fun z => Scheme.Modules.Hom.app θ ⊤ z)
    (pullbackGlobalSections_unitHomEquiv j M s).symm

/-- `Stacks.PullbackUnitComparisonSection.unitHomEquiv_eval_comp`, with the structure-sheaf
comparison spelled as the inverse of `Stacks.PullbackTensorCoherence.pullbackUnitComparison`. -/
theorem inv_pullbackUnitComparison_eval_comp (M : Y.Modules) (N : Y'.Modules) (s : M.sections)
    (θ : (Scheme.Modules.pullback j).obj M ⟶ N) :
    (N.unitHomEquiv (@inv _ _ _ _ (pullbackUnitComparison j.toLRSHom.toShHom)
            (isIso_pullbackUnitComparison _) ≫
          (Scheme.Modules.pullback j).map (M.unitHomEquiv.symm s) ≫ θ)).eval (op ⊤) =
      θ.app ⊤ (pullbackGlobalSections j M (s.eval (op ⊤))) :=
  unitHomEquiv_eval_comp j M N s θ

end Scheme

/-! ### The restriction of a degree-one form on projective space -/

section Projective

/-- If the morphism `sectionHom t` out of the unit is the pullback of `sectionHom s` along `g`,
precomposed with the inverse of the structure-sheaf comparison and followed by `θ`, then the value
of `t` over the top open is the image under `θ` of the geometric restriction of `s`. -/
theorem eval_top_of_sectionHom_eq (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)
    (θ : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) (t : (twistOver m S 1).sections)
    (hst : sectionHom (twistOver m S 1) t =
      (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ.hom) :
    t.eval (op ⊤) =
      θ.hom.app ⊤ (pullbackGlobalSections g (twistOver n S 1) (s.eval (op ⊤))) :=
  (congrArg (fun r : (twistOver m S 1).sections => r.eval (op ⊤))
      (((twistOver m S 1).unitHomEquiv.apply_symm_apply t).symm.trans
        (congrArg (twistOver m S 1).unitHomEquiv hst))).trans
    (unitHomEquiv_eval_comp g (twistOver n S 1) (twistOver m S 1) s θ.hom)

/-- Every global section `s` of `𝒪_{ℙⁿ}(1)` has a restriction `t` along `(g, θ)` whose value
over the top open is the image under `θ` of `AlgebraicGeometry.pullbackGlobalSections` of `s`,
and for every module `M`, pulling back multiplication by `s` and composing with the tensor
comparisons is multiplication by `t`. -/
theorem exists_pullback_mulSection_eval_top (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)
    (θ : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) :
    ∃ t : (twistOver m S 1).sections,
      t.eval (op ⊤) =
          θ.hom.app ⊤ (pullbackGlobalSections g (twistOver n S 1) (s.eval (op ⊤))) ∧
        ∀ M : (projectiveSpaceOver n S).Modules,
          (Scheme.Modules.pullback g).map (mulSection n S M s) ≫
              (pullbackTensorModulesIso g M (twistOver n S 1)).hom ≫
              (tensorModulesMapIso (projectiveSpaceOver m S)
                (Iso.refl ((Scheme.Modules.pullback g).obj M)) θ).hom =
            mulSection m S ((Scheme.Modules.pullback g).obj M) t :=
  ⟨(twistOver m S 1).unitHomEquiv
      ((Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ.hom),
    eval_top_of_sectionHom_eq n m S g θ s _ (Equiv.symm_apply_apply _ _),
    fun M => Stacks.AlgebraicGeometry.PullbackSectionMul.pullback_mulSection n m S g M θ s _
      (Equiv.symm_apply_apply _ _)⟩

end Projective

end Stacks.PullbackUnitComparisonSection

end
