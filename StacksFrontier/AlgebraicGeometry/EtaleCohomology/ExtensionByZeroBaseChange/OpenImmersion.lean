module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Cocontinuous
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero along an open immersion, in an arbitrary module universe

For a general étale `j : U ⟶ X` the presheaf extension by zero of a sheaf of `Λ`-modules is
`V ↦ ⨁_{V → U} F(V → U)`, and the indexing set of that coproduct is as large as the small
étale site, so `AlgebraicGeometry.moduleExtensionByZero` ties the module universe to the
universe of schemes.

When `j` is an open immersion it is a monomorphism, so there is at most one morphism `V ⟶ U`
over `X`, and the coproduct has at most one summand. The left Kan extension then exists
pointwise for a presheaf of modules in *any* universe: the indexing category of the colimit has
a terminal object when `V` does map to `U`, and is empty otherwise. Extension by zero along an
open immersion therefore exists at an independent module universe, together with its defining
adjunction.

## Main definitions

* `AlgebraicGeometry.moduleOpenExtensionByZero` — `j_!` on sheaves of `Λ`-modules in an
  arbitrary universe, for `j` an open immersion.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroAdjunction_unit_isIso` — along an open immersion
  the unit `F ⟶ j^{-1}j_!F` of the extension-by-zero adjunction is an isomorphism, so
  extension by zero is fully faithful.
* `AlgebraicGeometry.smallEtalePostcompose_hasPointwiseLeftKanExtension_of_isOpenImmersion` —
  the pointwise left Kan extension along composition with an open immersion exists for a
  presheaf of modules in any universe.
* `AlgebraicGeometry.moduleOpenExtensionByZeroAdjunction` — the adjunction `j_! ⊣ j^{-1}`.
* `AlgebraicGeometry.moduleOpenExtensionByZeroIso` — in a universe where the general
  construction is also available, the two agree.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) [IsOpenImmersion (B.inclusion.map U.obj.hom)] (Λ : Type v) [Ring Λ]

/-- Along an open immersion `U ⟶ X` the unit of the extension-by-zero adjunction is an
isomorphism: an abelian étale sheaf on `U` is recovered from its extension by zero by
restricting back to `U`. -/
@[stacks 0F70 "extension_by_zero_unit"]
public theorem abelianExtensionByZeroAdjunction_unit_isIso
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    IsIso ((abelianExtensionByZeroAdjunction B X hX U).unit.app F) := by
  have : Mono U.obj.hom := B.inclusion.mono_of_mono_map inferInstance
  have : IsIso (abelianExtensionByZeroAdjunction B X hX U).unit :=
    Functor.isIso_unit_of_sheafPushforwardContinuous (smallEtalePostcompose B X hX U)
      AddCommGrpCat.{u + 1} (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X hX) (abelianExtensionByZeroAdjunction B X hX U)
  infer_instance

/-- For an open immersion `U ⟶ X` the presheaf extension by zero has at most one summand, so
its pointwise left Kan extension exists for a presheaf of `Λ`-modules in any universe: the
category indexing the colimit at an étale `V ⟶ X` has a terminal object when `V` maps to `U`
over `X`, and is empty otherwise. -/
public theorem smallEtalePostcompose_hasPointwiseLeftKanExtension_of_isOpenImmersion
    (F : (SmallEtale B U.obj.left.1 U.obj.left.property)ᵒᵖ ⥤ ModuleCat.{w} Λ) :
    (smallEtalePostcompose B X hX U).op.HasPointwiseLeftKanExtension F := by
  classical
  have : Mono U.obj.hom := B.inclusion.mono_of_mono_map inferInstance
  intro V
  by_cases h : Nonempty (V.unop ⟶ U)
  · let f := h.some
    have hf : Etale (B.inclusion.map f.hom.left) := by
      apply MorphismProperty.of_postcomp @Etale (W' := @Etale)
        _ (B.inclusion.map U.obj.hom) inferInstance
      simpa only [← Functor.map_comp, Over.w] using V.unop.property
    let T : SmallEtale B U.obj.left.1 U.obj.left.property := ⟨Over.mk f.hom.left, hf⟩
    let e : (smallEtalePostcompose B X hX U).obj T ≅ V.unop :=
      (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
        (Over.isoMk (Iso.refl _) (by
          change 𝟙 _ ≫ V.unop.obj.hom = f.hom.left ≫ U.obj.hom
          simpa only [Category.id_comp] using (Over.w f.hom).symm))
    let A : CostructuredArrow (smallEtalePostcompose B X hX U).op V :=
      CostructuredArrow.mk e.inv.op
    let toA (Z : CostructuredArrow (smallEtalePostcompose B X hX U).op V) : Z ⟶ A :=
      CostructuredArrow.homMk
        ((smallEtalePostcompose B X hX U).preimage (e.hom ≫ Z.hom.unop)).op (by
          apply Quiver.Hom.unop_inj
          change e.inv ≫ (smallEtalePostcompose B X hX U).map
            ((smallEtalePostcompose B X hX U).preimage (e.hom ≫ Z.hom.unop)) = Z.hom.unop
          rw [Functor.map_preimage, Iso.inv_hom_id_assoc])
    have hA : IsTerminal A := by
      refine IsTerminal.ofUniqueHom toA fun Z φ => ?_
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply (smallEtalePostcompose B X hX U).map_injective
      apply (cancel_epi e.inv).1
      have hw (ψ : Z ⟶ A) : e.inv ≫ (smallEtalePostcompose B X hX U).map ψ.left.unop =
          Z.hom.unop := congrArg Quiver.Hom.unop (CostructuredArrow.w ψ)
      rw [hw φ, hw (toA Z)]
    exact HasColimit.mk ⟨_, colimitOfDiagramTerminal hA _⟩
  · have : IsEmpty (CostructuredArrow (smallEtalePostcompose B X hX U).op V) :=
      ⟨fun Z => h ⟨Z.hom.unop ≫
        ObjectProperty.homMk (Over.homMk Z.left.unop.obj.hom rfl)⟩⟩
    exact HasColimit.mk ⟨
      { pt := (⊥_ (ModuleCat.{w} Λ))
        ι := { app := fun Z => isEmptyElim Z
               naturality := fun {Z} _ _ => False.elim (IsEmpty.false Z) } },
      { desc := fun _ => 0
        fac := fun _ Z => isEmptyElim Z
        uniq := fun _ _ _ => Subsingleton.elim _ _ }⟩

/-- Along an open immersion the left Kan extension of a presheaf of `Λ`-modules exists with no
hypothesis on the module universe. -/
public instance smallEtalePostcompose_hasLeftKanExtension_of_isOpenImmersion
    (F : (SmallEtale B U.obj.left.1 U.obj.left.property)ᵒᵖ ⥤ ModuleCat.{w} Λ) :
    (smallEtalePostcompose B X hX U).op.HasLeftKanExtension F := by
  have := smallEtalePostcompose_hasPointwiseLeftKanExtension_of_isOpenImmersion B X hX U Λ F
  infer_instance

/-- Extension by zero of étale sheaves of `Λ`-modules along an open immersion `U ⟶ X`, in an
arbitrary module universe: the sheafification of the presheaf `V ↦ ⨁_{V → U} F(V → U)`, whose
coproduct has at most one summand ([Stacks, Tag 03S3], part (3)). -/
public def moduleOpenExtensionByZero
    [HasWeakSheafify (SmallEtale.topology B X hX) (ModuleCat.{w} Λ)] :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) (ModuleCat.{w} Λ) ⥤
      Sheaf (SmallEtale.topology B X hX) (ModuleCat.{w} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U) (ModuleCat.{w} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by zero along an open immersion is left adjoint to restriction. -/
@[stacks 03S3 "module_extension_by_zero"]
public def moduleOpenExtensionByZeroAdjunction
    [HasWeakSheafify (SmallEtale.topology B X hX) (ModuleCat.{w} Λ)] :
    moduleOpenExtensionByZero B X hX U Λ ⊣ moduleRestriction B X hX U Λ :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePostcompose B X hX U) (ModuleCat.{w} Λ)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by zero along an open immersion is a left adjoint, hence preserves colimits. -/
public instance moduleOpenExtensionByZero_isLeftAdjoint
    [HasWeakSheafify (SmallEtale.topology B X hX) (ModuleCat.{w} Λ)] :
    (moduleOpenExtensionByZero B X hX U Λ).IsLeftAdjoint :=
  (moduleOpenExtensionByZeroAdjunction B X hX U Λ).isLeftAdjoint

/-- In a module universe where extension by zero along an arbitrary étale morphism is also
available, the open-immersion construction agrees with it. -/
public def moduleOpenExtensionByZeroIso :
    moduleOpenExtensionByZero B X hX U Λ ≅ moduleExtensionByZero B X hX U Λ :=
  Adjunction.leftAdjointUniq (moduleOpenExtensionByZeroAdjunction B X hX U Λ)
    (moduleExtensionByZeroAdjunction B X hX U Λ)

end AlgebraicGeometry

end
