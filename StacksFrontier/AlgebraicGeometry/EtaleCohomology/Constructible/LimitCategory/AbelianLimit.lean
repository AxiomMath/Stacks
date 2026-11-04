module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianEssentiallyConstantColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.CoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleEssSurj
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageColimitCompletion
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles

/-!
# Constructible abelian sheaves on a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. The category of constructible abelian sheaves on
`X_étale` is the colimit of the categories of constructible abelian sheaves on the `(X_i)_étale`.
This is Stacks Tag 09YU, clause (2).

The source deduces it from clause (3): a constructible abelian sheaf on a quasi-compact scheme is
annihilated by some `n > 0`. Here abelian sheaves are read as sheaves of `ULift ℤ`-modules
(`AddCommGrpCat.moduleCatUliftIntEquivalence`), under which constructible abelian sheaves become
constructible module sheaves over the Noetherian ring `ULift ℤ`. Fullness passes along that
equivalence (`AlgebraicGeometry.smallEtaleStagesFull_of_coefficientEquivalence`); faithfulness is
the base's `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleAbelianSheaf`, proved
directly on abelian sheaves. For essential surjectivity,
a constructible abelian sheaf `F` on `X` annihilated by `n` is the inverse image of a constructible
module sheaf `M` at a stage, hence of `M/nM`, which is a constructible abelian sheaf because it is
annihilated by `n`.

## Main results

* `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleAbelianSheaf` (the base's, in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageColimitCompletion`),
  `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleAbelianSheaf_unconditional`,
  `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleAbelianSheaf_unconditional` — the three
  assertions.
* `AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleAbelianSheaf_unconditional` — **Tag
  09YU, clause (2).**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_addCommGrpCat

attribute [local instance 2000] isRightAdjoint_sheafPushforwardContinuous_uliftInt
  hasWeakSheafify_over_uliftInt

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

omit [Nonempty I] in
/-- **Stacks 09YU, clause (2), the fullness assertion.** -/
@[stacks 09YU "clause (2), the fullness assertion"]
theorem smallEtaleStagesFull_isConstructibleAbelianSheaf_unconditional (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) :=
  smallEtaleStagesFull_of_coefficientEquivalence B
    AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1} Dg c hX
    (fun X F hF => isConstructibleModuleSheaf_uliftIntEquivalence B X F hF)
    (smallEtaleStagesFull_isConstructibleModuleSheaf B (ULift.{u + 1} ℤ) Dg c hX hc haff hqc hqs)

/-- **Stacks 09YU, clause (2), the essential surjectivity assertion.** Every constructible abelian
sheaf on `X_étale` is isomorphic to the inverse image of a constructible abelian sheaf on some
`(X_i)_étale`. -/
@[stacks 09YU "clause (2), the essential surjectivity assertion"]
theorem smallEtaleStagesEssSurj_isConstructibleAbelianSheaf_unconditional (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) := by
  intro F hF
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := haff
  have : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hXc : CompactSpace (B.obj c.pt hX).obj :=
    Scheme.compactSpace_of_isLimit (Dg ⋙ B.inclusion) c hc
  have hXq : QuasiSeparatedSpace (B.obj c.pt hX).obj := by
    have := isAffineHom_π_app (Dg ⋙ B.inclusion) c hc (op (Classical.arbitrary I))
    have : QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj (op (Classical.arbitrary I))) := hqs _
    exact quasiSeparatedSpace_of_quasiSeparated (c.π.app (op (Classical.arbitrary I)))
  obtain ⟨n, hn, hFn⟩ :=
    exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B (B.obj c.pt hX) hXc hXq F hF
  let E := uliftIntSheafEquivalence B (B.obj c.pt hX)
  obtain ⟨i, M, hM, ⟨eM⟩⟩ := smallEtaleStagesEssSurj_isConstructibleModuleSheaf B (ULift.{u + 1} ℤ)
    Dg c hX hc haff hqc hqs _ (isConstructibleModuleSheaf_uliftIntEquivalence B _ F hF)
  refine ⟨i, _, isConstructibleAbelianSheaf_inverse_modulo B (Dg.obj (op i)) n hn.ne' M hM, ⟨?_⟩⟩
  let M' := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  let PiM := smallEtaleStageProjection B M' Dg c hX i
  have : PiM.Additive := additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ _
  have : PreservesColimitsOfSize.{0, 0} PiM :=
    (smallEtaleSheafAdjunction B M' (coneStageHom B Dg c hX i)).leftAdjoint_preservesColimits
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h3 : PiM.map (n • 𝟙 M) = n • 𝟙 (PiM.obj M) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  have h5 : n • 𝟙 (E.functor.obj F) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hFn, Functor.map_zero]
  have hw : (n • 𝟙 (PiM.obj M)) ≫ eM.hom = eM.hom ≫ (n • 𝟙 (E.functor.obj F)) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp]
    exact congrArg (n • ·) (Category.comp_id _).symm
  exact ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (coneStageHom B Dg c hX i))
      (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (SmallEtale.topology B c.pt hX)
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}.symm).app _).symm ≪≫
    E.inverse.mapIso (PreservesCokernel.iso PiM (n • 𝟙 M) ≪≫
      cokernelIsoOfEq h3 ≪≫ cokernel.mapIso _ _ eM eM hw ≪≫ cokernelIsoOfEq h5 ≪≫
      cokernelZeroIsoTarget) ≪≫
    (E.unitIso.app F).symm

/-- **Stacks 09YU, clause (2).** Let `X = lim X_i` be the limit of a directed inverse system of
schemes with affine transition morphisms, each `X_i` quasi-compact and quasi-separated. The
category of constructible abelian sheaves on `X_étale` is the colimit of the categories of
constructible abelian sheaves on the `(X_i)_étale`: the comparison is faithful, full and
essentially surjective. -/
@[stacks 09YU "clause (2)"]
theorem smallEtaleStagesColimit_isConstructibleAbelianSheaf_unconditional (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B AddCommGrpCat.{u + 1} Dg c hX
      (fun Y => IsConstructibleAbelianSheaf B Y) where
  faithful := smallEtaleStagesFaithful_isConstructibleAbelianSheaf B Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isConstructibleAbelianSheaf_unconditional B Dg c hX hc haff hqc hqs
  essSurj :=
    smallEtaleStagesEssSurj_isConstructibleAbelianSheaf_unconditional B Dg c hX hc haff hqc hqs

end AlgebraicGeometry
