module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.SymProjectiveBundleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenNatural
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.DegreeOne

/-!
# The projective bundle of a twist

Let `ℰ` be finite locally free and `ℒ` invertible on a scheme `X`. The projective bundle of
`ℰ ⊗ ℒ` is that of `ℰ`: there is an isomorphism `g : 𝐏(ℰ ⊗ ℒ) ≅ 𝐏(ℰ)` over `X`, and it carries
the twists as `𝒪_{𝐏(ℰ ⊗ ℒ)}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ`. This is [Stacks, Tag 02NC] for the
projective bundles `Stacks.Chow.bundle`.

The isomorphism is the glued chart comparison of `Stacks.SymProjectiveBundleTwist`: over an
affine open `W` on which a section `ℓ` generates `ℒ`, it is `Proj` of the identification
`Γ(W, Sym ℰ) ≅ Γ(W, Sym(ℰ ⊗ ℒ))`, `m ↦ m ⊗ ℓ` in degree one. The twists are compared on `𝐏(ℰ)`:
the tautological quotient of `ℰ ⊗ ℒ` pulled back along `g⁻¹` and the twisted tautological
quotient `π^*(ℰ ⊗ ℒ) ≅ π^*ℰ ⊗ π^*ℒ ⟶ 𝒪(1) ⊗ π^*ℒ` are two invertible quotients of one module,
and on the chart over `W` the second factors through the first: both send the pullback of
`m ⊗ ℓ` to the homogeneous-section value of `m`, the second tensored with the pullback of `ℓ`
(`Stacks.Chow.GenuineChern.exists_chart_tensorFactorization`). Two invertible quotients that
agree locally are isomorphic (`Stacks.Chow.GenuineChern.existsUnique_iso_of_pullback`).

## Main definitions

* `Stacks.Chow.GenuineChern.bundleTensorHom` — the comparison `𝐏(ℰ ⊗ ℒ) ⟶ 𝐏(ℰ)`.
* `Stacks.Chow.GenuineChern.tensorTwistQuotient` — the twisted tautological quotient.
* `Stacks.Chow.GenuineChern.rightTensorSection` — tensoring with a global section.

## Main results

* `Stacks.Chow.GenuineChern.chart_inv_bundleTensorHom` — the inverse comparison on a chart.
* `Stacks.Chow.GenuineChern.exists_chart_tensorFactorization` — the local factorization.
* `Stacks.Chow.GenuineChern.exists_bundleTensorIso` — Stacks 02NC with the twists.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Chow.GenuineChern

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

-- `Tensor.ringSheaf` is the remaining definition in the bridge between the two namings of the
-- structure sheaf, and it is seated one level lower than the two above, at
-- `instance_reducible`, because every fault it answers for here lives at `.instances`
-- transparency.  Per Lean's reducibility attributes, `implicitReducible` unfolds at
-- `TransparencyMode.implicit`, *strictly above* `.instances`, while `instanceReducible`
-- unfolds at `.instances` and at every level above it, and `.instances` is where instance
-- search runs.  Left semireducible, `Tensor.ringSheaf X.sheaf` is not visibly
-- `X.ringCatSheaf` to instance search, so the twist `(sheafTensor X.sheaf).obj E).obj L` --
-- which the statements below hand to `bundle`, `bundleProj`, `bundleTwist` and `bundlePieces`
-- at `X.Modules = SheafOfModules X.ringCatSheaf` -- could reach neither
-- `isFiniteLocallyFree_sheafTensor` just below nor the `IsQuasicoherent` instance derived from
-- it, and `chartGradedInv`/`chartGradedHom` were left ambiguous against their `SymGraded`
-- namesakes for want of those arguments.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance]
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree

/-- The `Stacks` spelling of invertibility, from the `AlgebraicGeometry` one. -/
local instance isInvertible_stacks {X : Scheme.{u}} (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h

variable {X : Scheme.{u}} (E L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- A twist of a finite locally free module by an invertible module is finite locally free. -/
instance isFiniteLocallyFree_sheafTensor :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) :=
  haveI := Stacks.Chow.isFiniteLocallyFreeOfRank_one_of_isInvertible L
  Stacks.Chow.isFiniteLocallyFree_tensor inferInstance
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1)


/-! ### Tensoring with a global section -/

section RightTensor

variable {Q : Scheme.{u}} (M K : Q.Modules) (s₀ : Γ(K, ⊤))

/-- **Tensoring with a global section**: `a ↦ a ⊗ s₀ : M ⟶ M ⊗ K`. -/
def rightTensorSection : M ⟶ Scheme.Modules.tensorObj M K :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Q.sheaf.obj Q.ringCatSheaf.property
      M).inv ≫
    Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorMap Q.sheaf.obj Q.ringCatSheaf.property (𝟙 M)
      (K.unitHomEquiv.symm ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal K
        (Limits.isTerminalTop (α := Q.Opens))).symm s₀))

/-- Tensoring with a global section, on global sections. -/
theorem rightTensorSection_app (a : Γ(M, ⊤)) :
    (rightTensorSection M K s₀).val.app (op ⊤) a =
      Stacks.SheafOfModules.tensorSectionsAt Q.sheaf.obj Q.ringCatSheaf.property
        (op ⊤) M K a s₀ := by
  change (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorMap Q.sheaf.obj Q.ringCatSheaf.property
      (𝟙 M) _).val.app (op ⊤)
    ((Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Q.sheaf.obj Q.ringCatSheaf.property
      M).inv.val.app (op ⊤) a) = _
  refine (congrArg _ (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSections_rightUnitorInvAt
    Q.sheaf.obj Q.ringCatSheaf.property (op ⊤) M a)).trans ?_
  refine (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorMap_app Q.sheaf.obj
    Q.ringCatSheaf.property (𝟙 M) _ (op ⊤) a _).trans ?_
  congr 1
  exact (one_smul (Q.ringCatSheaf.obj.obj (op ⊤))
    (((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal K
      (Limits.isTerminalTop (α := Q.Opens))).symm s₀).eval (op ⊤))).trans
    ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal K
      (Limits.isTerminalTop (α := Q.Opens))).apply_symm_apply s₀)

end RightTensor

/-- The tensor product of two morphisms, on the section coming from a pure tensor. -/
theorem tensorSheafMap_toTensorSheafSection {Z : Scheme.{u}} {A A' B B' : Z.Modules}
    (f : A ⟶ A') (g : B ⟶ B') (V : Z.Opens) (a : Γ(A, V)) (b : Γ(B, V)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Z.toRingedSpace.sheaf)).map ((f, g) : (A, B) ⟶ (A', B'))).val.app (op V)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z.toRingedSpace A B
          (op V) (a ⊗ₜ b)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z.toRingedSpace A' B'
        (op V) (f.val.app (op V) a ⊗ₜ g.val.app (op V) b) :=
  Stacks.RingedSpace.tensorSheaf_map_unit_tmul Z.toRingedSpace f g (op V) a b

/-- The tensor product of a morphism with the identity, on the section coming from a pure
tensor: the case of `tensorSheafMap_toTensorSheafSection` at `g = 𝟙 B`, in the uncurried
spelling `((sheafTensor _).map f).app B`. -/
theorem tensorSheafMap_toTensorSheafSection_id {Z : Scheme.{u}} {A A' B : Z.Modules}
    (f : A ⟶ A') (V : Z.Opens) (a : Γ(A, V)) (b : Γ(B, V)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).map f).app B).val.app (op V)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z.toRingedSpace A B
          (op V) (a ⊗ₜ b)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z.toRingedSpace A' B
        (op V) (f.val.app (op V) a ⊗ₜ b) := by
  have tensorWithIdentity :
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Z.toRingedSpace.sheaf)).map ((f, 𝟙 B) : (A, B) ⟶ (A', B)) =
        ((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).map f).app B :=
    (congrArg (fun k ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor
          Z.toRingedSpace.sheaf).map f).app B ≫ k)
        (((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).obj A').map_id B)).trans
      (Category.comp_id _)
  exact (congrArg (fun morphism ↦ morphism.val.app (op V)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z.toRingedSpace A B
          (op V) (a ⊗ₜ b))) tensorWithIdentity.symm).trans
    (Stacks.RingedSpace.tensorSheaf_map_unit_tmul Z.toRingedSpace f (𝟙 B) (op V) a b)

/-! ### The twisted tautological quotient -/

section TensorQuotient

open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
  Stacks.AlgebraicGeometry.ProjTwistSections Stacks.SymGraded
  Stacks.AlgebraicGeometry.RelativeProjTwistGlue

variable {X : Scheme.{u}} {E L : X.Modules} [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E)

/-- **The tautological quotient of `ℰ`, twisted by `ℒ`**: on `𝐏(ℰ)`,
`π^*(ℰ ⊗ ℒ) ≅ π^*ℰ ⊗ π^*ℒ ⟶ 𝒪(1) ⊗ π^*ℒ`, read out of `π^*(𝟙^*(ℰ ⊗ ℒ))`. -/
def tensorTwistQuotient :
    (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
        ((Scheme.Modules.pullback (𝟙 X)).obj (Stacks.SymTwistChart.tensorObj E L)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
            (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L) :=
  (Scheme.Modules.pullback _).map
      ((Scheme.Modules.pullbackId X).hom.app (Stacks.SymTwistChart.tensorObj E L)) ≫
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E L).hom ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
          (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).map
        (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).app
      ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)

instance epi_tensorTwistQuotient : Epi (tensorTwistQuotient (L := L) hqc) := by
  have h2 : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).map
        (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).app
      ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
        L)) := by
    have h := @Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace _ _ _ _
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)
      (𝟙 ((Scheme.Modules.pullback
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L))
      (Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E hqc)
      ⟨fun _ _ w ↦ (Category.id_comp _).symm.trans (w.trans (Category.id_comp _))⟩
    have identityLeg : ((Stacks.SheafOfModules.Tensor.sheafTensor
            (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).app
            ((Scheme.Modules.pullback
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor
              (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).map
            (𝟙 ((Scheme.Modules.pullback
              (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)) =
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).app
          ((Scheme.Modules.pullback
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L) :=
      (congrArg (fun k ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor
              (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).app
              ((Scheme.Modules.pullback
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L) ≫ k)
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).map_id
              ((Scheme.Modules.pullback
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L))).trans
        (Category.comp_id _)
    exact identityLeg ▸ h
  have h3 : Epi (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E L).hom :=
    ⟨fun _ _ w ↦ (Iso.cancel_iso_hom_left _ _ _).1 w⟩
  have h4 : Epi
      ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).map
        ((Scheme.Modules.pullbackId X).hom.app (Stacks.SymTwistChart.tensorObj E L))) :=
    (((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).mapIso
      ((Scheme.Modules.pullbackId X).app
        (Stacks.SymTwistChart.tensorObj E L))).isIso_hom).epi_of_iso
  exact epi_comp' h4 (epi_comp' h3 h2)

omit [E.IsQuasicoherent] in
/-- **Morphisms out of a module pulled back to a chart are determined by pulled-back
sections.** On the chart of `𝐏(ℰ)` over an affine open `U`, two morphisms out of the pullback of
a quasi-coherent `ℱ` on `X` agree as soon as they agree on the pullbacks of the sections of `ℱ`
over `U`. -/
theorem chart_pullback_hom_ext {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {N : (AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra E hqc).grading U)).Modules}
    (f g :
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Scheme.Modules.pullback (𝟙 X)).obj F)) ⟶ N)
    (hfg : ∀ y : Γ(F, U),
      resTop N (top_le_chart_preimage _ hqc U hU)
          (f.val.app (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ (𝟙 X ⁻¹ᵁ U))))
            (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) _ _
              (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase _ _
                (unitSection (𝟙 X) F U y)))) =
        resTop N (top_le_chart_preimage _ hqc U hU)
          (g.val.app (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ (𝟙 X ⁻¹ᵁ U))))
            (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) _ _
              (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase _ _
                (unitSection (𝟙 X) F U y))))) :
    f = g := by
  have hFU : ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ≫
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X) ⁻¹ᵁ U = ⊤ :=
    top_le_iff.mp (top_le_chart_preimage _ hqc U hU)
  let κ : (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ≫
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X)).obj F ⟶
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Scheme.Modules.pullback (𝟙 X)).obj F)) :=
    (Scheme.Modules.pullbackComp ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X)).inv.app F ≫
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).map
        ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
          (𝟙 X)).inv.app F)
  have : IsIso κ :=
    (((Scheme.Modules.pullbackComp ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X)).app F).symm ≪≫
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).mapIso
        ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
          (𝟙 X)).app F).symm).isIso_hom
  refine (IsIso.epi_of_iso κ).left_cancellation _ _ ?_
  refine pullback_hom_ext_of_isAffineOpen _ hU hFU F fun y => ?_
  have hk : κ.val.app (op (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ≫
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X) ⁻¹ᵁ U))
        (unitSection _ F U y) =
      unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) _ _
        (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase _ _
          (unitSection (𝟙 X) F U y)) :=
    (congrArg (((Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U
        hU)).map
          ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
            (𝟙 X)).inv.app F)).val.app _)
      (pullbackComp_inv_unitSection _ _ F U y)).trans
      ((unitSection_pullback_map _ _ _ _).trans
        (congrArg _ (pullbackComp_inv_unitSection _ (𝟙 X) F U y)))
  refine ((comp_app_apply κ _ _ _).trans (congrArg _ hk)).trans
    (Eq.trans ?_ ((comp_app_apply κ _ _ _).trans (congrArg _ hk)).symm)
  exact resTop_injective _ (top_le_chart_preimage _ hqc U hU) (hfg y)

omit [E.IsQuasicoherent] in
/-- **The twisted quotient at a pulled-back pure tensor.** -/
theorem tensorTwistQuotient_unitSection {U : X.Opens} (m : Γ(E, U)) (ℓ : Γ(L, U)) :
    (tensorTwistQuotient (L := L) hqc).val.app
      (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ (𝟙 X ⁻¹ᵁ U)))
      (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase _ _
        (unitSection (𝟙 X) (Stacks.SymTwistChart.tensorObj E L) U
          (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
            E L m ℓ))) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)
        (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        ((((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m)) ⊗ₜ
          unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase L U ℓ) := by
  refine (comp_app_apply _ _ _ _).trans ?_
  refine (congrArg _ ((unitSection_pullback_map _ _ _ _).trans
    (congrArg _ (pullbackId_hom_unitSection X _ U _)))).trans ?_
  refine (comp_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit
    (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E L U m ℓ)).trans ?_
  refine (tensorSheafMap_toTensorSheafSection_id
    (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc) _ _ _).trans ?_
  exact congrArg (fun z ↦ Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection _ _ _
    _ (z ⊗ₜ _)) (tautologicalMap_unitSection E hqc U m)

omit [E.IsQuasicoherent] in
/-- **The twisted quotient on a chart, at a pulled-back pure tensor.** On the chart of `𝐏(ℰ)`
over an affine open `U`, the twisted tautological quotient carries the pullback of `m ⊗ ℓ` to the
pullback of the homogeneous-section value of `m` tensored with the pullback of `ℓ`. -/
theorem tensorTwistQuotient_chart_apply {U : X.Opens} (hU : IsAffineOpen U) (m : Γ(E, U))
    (ℓ : Γ(L, U)) :
    resTop _ (top_le_chart_preimage _ hqc U hU)
        (((Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).map
          (tensorTwistQuotient (L := L) hqc)).val.app
          (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ (𝟙 X ⁻¹ᵁ U))))
          (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) _ _
            (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase _ _
              (unitSection (𝟙 X) (Stacks.SymTwistChart.tensorObj E L) U
                (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
                  E L m ℓ))))) =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
            L)).inv.val.app (op ⊤)
        (Stacks.SheafOfModules.tensorSectionsAt
          (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading U)).sheaf.obj
          (AlgebraicGeometry.Proj
            ((schemeSheafGradedAlgebra E hqc).grading U)).ringCatSheaf.property
          (op ⊤) _ _
          (resTop _ (top_le_chart_preimage _ hqc U hU)
            (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
              ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
              (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
                ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m))))
          (resTop _ (top_le_chart_preimage _ hqc U hU)
            (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
              ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
                L)
              ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
              (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase L U ℓ)))) := by
  have hq := tensorTwistQuotient_unitSection hqc m ℓ
  refine (congrArg (resTop _ _) ((unitSection_pullback_map _ _ _ _).trans
    (congrArg _ hq))).trans ?_
  have hc := Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
      ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m))
    (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase L U ℓ)
  have hc' := (congrArg ((Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
      L)).inv.val.app _) hc).symm.trans (Stacks.Chow.GenuineChern.iso_inv_hom_val_app _ _ _)
  refine (congrArg (resTop _ _) hc'.symm).trans ?_
  refine (app_resTop _ _ _).symm.trans ?_
  congr 1
  exact Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality _ _ _ _ _ _ _

variable [(Stacks.SymTwistChart.tensorObj E L).IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces (Stacks.SymTwistChart.tensorObj E L))
  (h : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L) hqc')).scheme)
  (hh : h ≫ (relativeProj (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
      hqc')).toBase = (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ≫ 𝟙 X)
  {U : X.Opens} (hU : IsAffineOpen U)
  (φ : (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L) hqc').grading U →+*ᵍ
    (schemeSheafGradedAlgebra E hqc).grading U)
  (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U) ≤
    (HomogeneousIdeal.irrelevant
      ((schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L) hqc').grading U)).map φ)
  (hc : (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ≫ h =
    AlgebraicGeometry.Proj.map φ hφ ≫
      (relativeProj (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L) hqc')).chart
        U hU)
  (ℓ : Γ(L, U))
  (hsurj : ∀ y : Γ(Stacks.SymTwistChart.tensorObj E L, U), ∃ m : Γ(E, U),
    y = Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) E L m ℓ)
  (hdeg : ∀ m : Γ(E, U),
    φ (DirectSum.of ((schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
        hqc').sectionPieces U) 1
      ((Scheme.Modules.symmetricAlgebraGen X (Stacks.SymTwistChart.tensorObj E L)).val.app (op U)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) E L m
          ℓ))) =
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m))

omit [E.IsQuasicoherent] in
include hc hsurj hdeg in
/-- **The local factorization of the twisted quotient.** On the chart of `𝐏(ℰ)` over an affine
open `U` on which `ℓ` generates `ℒ`, and over which `h : 𝐏(ℰ) ⟶ 𝐏(ℰ ⊗ ℒ)` is `Proj` of a graded
map carrying the degree-one element of `m ⊗ ℓ` to that of `m`, the twisted tautological quotient
factors through the pulled-back tautological quotient of `ℰ ⊗ ℒ`. -/
theorem exists_chart_tensorFactorization :
    ∃ ψ : (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        ((Scheme.Modules.pullback h).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist
            (Stacks.SymTwistChart.tensorObj E L) hqc')) ⟶
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
              (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.toRingedSpace.sheaf).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).obj
          ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj
            L)),
    (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).map
        (twistQuotientPullback (𝟙 X) hqc' hqc h hh) ≫ ψ =
    (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).map
        (tensorTwistQuotient (L := L) hqc) := by
  obtain ⟨Λ, hΛ⟩ := exists_chartTwistComparison hqc' hqc hU hU φ hφ
  have hT := top_le_chart_preimage _ hqc U hU
  -- the section `ℓ`, pulled back to the chart
  let s₀ := resTop _ hT (unitSection ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
    ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase L U ℓ))
  let ti := (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj L)).inv
  refine ⟨squarePullbackRestrict _ h _ _ hc _ ≫ Λ ≫ rightTensorSection _ _ s₀ ≫ ti, ?_⟩
  refine chart_pullback_hom_ext hqc hU _ _ fun y => ?_
  obtain ⟨m, rfl⟩ := hsurj y
  refine Eq.trans ?_ (tensorTwistQuotient_chart_apply hqc hU m ℓ).symm
  have h₂ := top_le_chart_preimage _ hqc' U hU
  have hL := chartFactorization_lhs (𝟙 X) hqc' hqc h hh hU hU φ hφ hc _ m Λ h₂ hT
    (hΛ _ m (hdeg m) h₂ hT) hT
  refine (congrArg (resTop _ _) (comp_app_apply _ _ _ _)).trans ?_
  refine (congrArg (resTop _ _) (comp_app_apply _ _ _ _)).trans ?_
  refine (congrArg (resTop _ _) (comp_app_apply _ _ _ _)).trans ?_
  refine (app_resTop _ _ _).symm.trans ?_
  refine (congrArg (fun x ↦ (rightTensorSection _ _ s₀ ≫ ti).val.app (op ⊤) x) hL).trans ?_
  exact congrArg (ti.val.app (op ⊤)) (rightTensorSection_app _ _ s₀ _)

end TensorQuotient

/-! ### The comparison morphism -/

open Stacks.AlgebraicGeometry.RelativeProj Stacks.SymGraded
  Stacks.AlgebraicGeometry.TrivializingSite in
/-- **The comparison morphism `𝐏(ℰ ⊗ ℒ) ⟶ 𝐏(ℰ)` of Stacks 02NC**: the chart comparisons of
`Stacks.SymProjectiveBundleTwist` over the affine opens trivializing `ℒ`, glued. -/
def bundleTensorHom :
    bundle (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) ⟶ bundle E :=
  Stacks.AlgebraicGeometry.RelativeProjDescent.desc L
    (Stacks.SymProjectiveBundleTwist.chartIso E L)
    (fun h ↦ Stacks.SymProjectiveBundleTwist.chartIso_naturality E L h)

/-- The comparison morphism is an isomorphism. -/
instance isIso_bundleTensorHom : IsIso (bundleTensorHom E L) :=
  Stacks.AlgebraicGeometry.RelativeProjDescent.isIso_desc L
    (Stacks.SymProjectiveBundleTwist.chartIso E L)
    (Stacks.SymProjectiveBundleTwist.chartIso_hom_toBase E L)
    (fun h ↦ Stacks.SymProjectiveBundleTwist.chartIso_naturality E L h)

/-- The comparison morphism is a morphism over `X`. -/
@[reassoc]
theorem bundleTensorHom_bundleProj :
    bundleTensorHom E L ≫ bundleProj E =
      bundleProj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) :=
  Stacks.AlgebraicGeometry.RelativeProjDescent.desc_relativeProjToBase L
    (Stacks.SymProjectiveBundleTwist.chartIso E L)
    (Stacks.SymProjectiveBundleTwist.chartIso_hom_toBase E L)
    (fun h ↦ Stacks.SymProjectiveBundleTwist.chartIso_naturality E L h)

open Stacks.SymTwistChart in
/-- The inverse of the chart comparison of Stacks 02NC is `Proj` of the inverse comparison of
graded rings of sections. -/
theorem chartProjIso_inv_eq_map {E L : X.Modules} [E.IsQuasicoherent]
    [(Stacks.SymTwistChart.tensorObj E L).IsQuasicoherent]
    (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
    (hqcEL : Stacks.SymGraded.IsQuasicoherentPieces (Stacks.SymTwistChart.tensorObj E L))
    {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hUaff : IsAffineOpen U) :
    (chartProjIso E L hqcE hqcEL e hUaff).inv =
      AlgebraicGeometry.Proj.map (chartGradedInv E L hqcE hqcEL e hUaff)
        (Stacks.AlgebraicGeometry.ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _
          (chartGradedInv E L hqcE hqcEL e hUaff) (chartGradedHom E L hqcE hqcEL e hUaff)
          (chartGradedInv_hom E L hqcE hqcEL e hUaff)) :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _
    (chartGradedInv E L hqcE hqcEL e hUaff) _
    (Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (Stacks.AlgebraicGeometry.ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _
        (chartGradedInv E L hqcE hqcEL e hUaff) (chartGradedHom E L hqcE hqcEL e hUaff)
        (chartGradedInv_hom E L hqcE hqcEL e hUaff)))

open Stacks.AlgebraicGeometry.RelativeProj Stacks.SymGraded
  Stacks.AlgebraicGeometry.TrivializingSite Stacks.SymTwistChart in
/-- **The inverse of the comparison on a chart**: over an affine open `W` trivializing `ℒ`, the
inverse of `Stacks.Chow.GenuineChern.bundleTensorHom` is `Proj` of the inverse comparison of the
graded rings of sections of `Sym(ℰ)` and `Sym(ℰ ⊗ ℒ)` over `W`. -/
theorem chart_inv_bundleTensorHom (W : Site L) :
    (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).chart W.1.1 W.1.2 ≫
        (asIso (bundleTensorHom E L)).inv =
      AlgebraicGeometry.Proj.map
          (chartGradedInv E L (bundlePieces E)
            (bundlePieces (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L))
            W.2.some W.1.2)
          (Stacks.AlgebraicGeometry.ProjPolynomialSections.irrelevant_le_map_of_graded_section _ _
            (chartGradedInv E L (bundlePieces E)
              (bundlePieces (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L))
              W.2.some W.1.2)
            (chartGradedHom E L (bundlePieces E)
              (bundlePieces (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L))
              W.2.some W.1.2)
            (chartGradedInv_hom E L (bundlePieces E)
              (bundlePieces (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L))
              W.2.some W.1.2)) ≫
        (relativeProj (schemeSheafGradedAlgebra
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L)
            (bundlePieces _))).chart W.1.1 W.1.2 := by
  have h1 := Stacks.AlgebraicGeometry.RelativeProjDescent.chart_desc L
    (Stacks.SymProjectiveBundleTwist.chartIso E L)
    (fun h ↦ Stacks.SymProjectiveBundleTwist.chartIso_naturality E L h) W
  have key := chartProjIso_inv_eq_map (bundlePieces E)
    (bundlePieces (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L)) W.2.some W.1.2
  have h2 : (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).chart W.1.1 W.1.2 =
      ((Stacks.SymProjectiveBundleTwist.chartIso E L W).inv ≫
        (relativeProj (schemeSheafGradedAlgebra
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L)
            (bundlePieces _))).chart W.1.1 W.1.2) ≫ (asIso (bundleTensorHom E L)).hom :=
    ((congrArg (fun k ↦ (Stacks.SymProjectiveBundleTwist.chartIso E L W).inv ≫ k) h1).trans
      (Iso.inv_hom_id_assoc _ _)).symm.trans (Category.assoc _ _ _).symm
  exact ((Iso.comp_inv_eq _).mpr h2).trans (congrArg (fun k ↦ k ≫ _) key)

open Stacks.AlgebraicGeometry.RelativeProj Stacks.SymGraded
  Stacks.AlgebraicGeometry.TrivializingSite Stacks.SymTwistChart in
/-- **The degree-one part of the inverse chart comparison**: it carries the degree-one element of
`m ⊗ ℓ` to that of `m`, for `ℓ` the generator of the trivialization. -/
theorem chartGradedInv_symmetricAlgebraGen {E L : X.Modules} [E.IsQuasicoherent]
    [(Stacks.SymTwistChart.tensorObj E L).IsQuasicoherent]
    (hqcE : IsQuasicoherentPieces E)
    (hqcEL : IsQuasicoherentPieces (Stacks.SymTwistChart.tensorObj E L))
    {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hUaff : IsAffineOpen U) (m : Γ(E, U)) :
    chartGradedInv E L hqcE hqcEL e hUaff
        (DirectSum.of ((schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
          hqcEL).sectionPieces U) 1
          ((Scheme.Modules.symmetricAlgebraGen X (Stacks.SymTwistChart.tensorObj E L)).val.app
            (op U) (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
              (op U) E L m (generator L e)))) =
      DirectSum.of ((schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m) := by
  have h1 := chartRingEquiv_of_symOne E L hqcE hqcEL e hUaff m
  have h2 : symOne E hqcE m = (Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) m :=
    (Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq E U m).symm
  have h3 : symOne (Stacks.SymTwistChart.tensorObj E L) hqcEL (sectionsEquiv E L e m) =
      (Scheme.Modules.symmetricAlgebraGen X (Stacks.SymTwistChart.tensorObj E L)).val.app (op U)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
          (op U) E L m (generator L e)) :=
    ((Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq _ U _).symm).trans
      (congrArg _ (sectionsEquiv_apply E L e m))
  rw [h2, h3] at h1
  change (chartRingEquiv E L hqcE hqcEL e hUaff).symm _ = _
  rw [← h1, RingEquiv.symm_apply_apply]

open Stacks.AlgebraicGeometry.RelativeProj Stacks.SymGraded
  Stacks.AlgebraicGeometry.TrivializingSite Stacks.SymTwistChart in
/-- **The twist of `𝐏(ℰ ⊗ ℒ)` pulled back to `𝐏(ℰ)`**: along the inverse of the comparison
morphism, `𝒪_{𝐏(ℰ ⊗ ℒ)}(1)` pulls back to `𝒪_{𝐏(ℰ)}(1) ⊗ π^*ℒ`. -/
theorem nonempty_pullback_inv_bundleTensorHom_iso :
    Nonempty ((Scheme.Modules.pullback (asIso (bundleTensorHom E L)).inv).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist (Stacks.SymTwistChart.tensorObj E L)
          (isQuasicoherentPieces_of_isQuasicoherent _)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
            (relativeProj (schemeSheafGradedAlgebra E
              (bundlePieces E))).scheme.toRingedSpace.sheaf).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E (bundlePieces E))).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E
          (bundlePieces E))).toBase).obj L)) := by
  have hh : (asIso (bundleTensorHom E L)).inv ≫
      (relativeProj (schemeSheafGradedAlgebra (Stacks.SymTwistChart.tensorObj E L)
        (isQuasicoherentPieces_of_isQuasicoherent _))).toBase =
      (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).toBase ≫ 𝟙 X :=
    ((Iso.inv_comp_eq _).mpr (bundleTensorHom_bundleProj E L).symm).trans
      (Category.comp_id _).symm
  have hj : ⨆ W : Site L, ((relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).chart
      W.1.1 W.1.2).opensRange = ⊤ := by
    simp_rw [Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.opensRange_chart]
    exact Stacks.AlgebraicGeometry.RelativeProjDescent.iSup_preimage_toOpens_eq_top L
  have : (Stacks.SymTwistChart.tensorObj E L).IsQuasicoherent :=
    Stacks.SymProjectiveBundleTwist.isQuasicoherent_tensorObj E L
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).scheme.sheaf.obj
      (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).scheme.ringCatSheaf.property
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E (bundlePieces E)) :=
    Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist _ _
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).scheme.sheaf.obj
      (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).scheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E
        (bundlePieces E))).toBase).obj L) :=
    isInvertible_pullback _ L
  obtain ⟨φ, -, -⟩ := @existsUnique_iso_of_pullback _ _ _ _ _ _
    (fun W : Site L ↦ (relativeProj (schemeSheafGradedAlgebra E (bundlePieces E))).chart
      W.1.1 W.1.2) _ hj
    (twistQuotientPullback (𝟙 X) (isQuasicoherentPieces_of_isQuasicoherent _) (bundlePieces E)
      (asIso (bundleTensorHom E L)).inv hh)
    (epi_twistQuotientPullback (𝟙 X) (isQuasicoherentPieces_of_isQuasicoherent _)
      (bundlePieces E) (asIso (bundleTensorHom E L)).inv hh)
    (tensorTwistQuotient (L := L) (bundlePieces E))
    (epi_tensorTwistQuotient (L := L) (bundlePieces E))
    (Stacks.RelativeProj.isInvertible_pullback_obj _ _
      (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist _ _))
    (by exact (Stacks.Chow.isInvertible_tensorObj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E (bundlePieces E))
      ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E
        (bundlePieces E))).toBase).obj L)))
    (fun W ↦ exists_chart_tensorFactorization (bundlePieces E)
      (isQuasicoherentPieces_of_isQuasicoherent _) (asIso (bundleTensorHom E L)).inv hh W.1.2
      (chartGradedInv E L (bundlePieces E) (isQuasicoherentPieces_of_isQuasicoherent _)
        W.2.some W.1.2) _ (chart_inv_bundleTensorHom E L W) (generator L W.2.some)
      (fun y ↦ ⟨(sectionsEquiv E L W.2.some).symm y,
        ((LinearEquiv.apply_symm_apply _ y).symm.trans (sectionsEquiv_apply E L W.2.some _))⟩)
      (fun m ↦ chartGradedInv_symmetricAlgebraGen _ _ W.2.some W.1.2 m))
  exact ⟨φ⟩

/-- **Stacks 02NC for projective bundles, with the twists.** There is an isomorphism
`g : 𝐏(ℰ ⊗ ℒ) ⟶ 𝐏(ℰ)` over `X` with `𝒪_{𝐏(ℰ ⊗ ℒ)}(1) ≅ g^*𝒪_{𝐏(ℰ)}(1) ⊗ π'^*ℒ`. -/
theorem exists_bundleTensorIso :
    ∃ g : bundle (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) ⟶ bundle E,
      IsIso g ∧ g ≫ bundleProj E =
          bundleProj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) ∧
        Nonempty (bundleTwist (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) ≅
          Scheme.Modules.tensorObj ((Scheme.Modules.pullback g).obj (bundleTwist E))
            ((Scheme.Modules.pullback
              (bundleProj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L))).obj
                L)) := by
  obtain ⟨τ⟩ := nonempty_pullback_inv_bundleTensorHom_iso E L
  refine ⟨bundleTensorHom E L, inferInstance, bundleTensorHom_bundleProj E L, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    (Scheme.Modules.pullbackCongr (asIso (bundleTensorHom E L)).hom_inv_id.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (bundleTensorHom E L) (asIso (bundleTensorHom E L)).inv).app
      _).symm ≪≫
    (Scheme.Modules.pullback (bundleTensorHom E L)).mapIso τ ≪≫
    Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (bundleTensorHom E L) _ _ ≪≫
    Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl _)
      ((Scheme.Modules.pullbackComp (bundleTensorHom E L) (bundleProj E)).app L ≪≫
        (Scheme.Modules.pullbackCongr (bundleTensorHom_bundleProj E L)).app L)

end Stacks.Chow.GenuineChern

end
