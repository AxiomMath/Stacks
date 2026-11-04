module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula

/-!
# Exactness properties of restriction, direct image and extension by zero

Let `j : U ⟶ X` be an étale morphism of schemes and let `j^{-1}`, `j_*` and `j_!` be
restriction, direct image and extension by zero on abelian sheaves of the small étale sites.
Restriction preserves all limits and all colimits, `j_!` preserves all colimits and all finite
limits (Stacks Tag 03S5), `j_*` preserves all limits, and all three are additive.  When `j` is
moreover a monomorphism, the counit `j^{-1} j_* F ⟶ F` is an isomorphism, the first of the two
isomorphisms of Stacks Tag 0F70.

## Main results

* `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_faithful` and
  `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_full`: composition with an étale morphism is
  faithful, and full as soon as the morphism is a monomorphism.
* `Stacks.EtaleCohomology.etaleRestriction_preservesLimits` and
  `Stacks.EtaleCohomology.etaleRestriction_preservesColimits`: restriction along an étale
  morphism is exact.
* `Stacks.EtaleCohomology.extensionByZero_preservesColimits` and
  `Stacks.EtaleCohomology.etaleDirectImage_preservesLimits`: `j_!` is right exact and `j_*` is
  left exact.
* `Stacks.EtaleCohomology.extensionByZero_preservesMonomorphisms`,
  `Stacks.EtaleCohomology.extensionByZero_preservesFiniteLimits` and
  `Stacks.EtaleCohomology.extensionByZero_exact`: `j_!` is exact.
* `Stacks.EtaleCohomology.directImageRestrictionIso`: for `j` a monomorphism, the natural
  isomorphism `j^{-1} j_* ≅ 𝟭`, given by the counit of `j^{-1} ⊣ j_*`.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 0F70](https://stacks.math.columbia.edu/tag/0F70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w w'

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Composition with an étale morphism is faithful. -/
instance smallEtaleCompose_faithful : (smallEtaleCompose j).Faithful where
  map_injective h := MorphismProperty.Over.Hom.ext (congrArg (fun k => k.left) h)

/-- Composition with a monomorphic étale morphism is full. -/
instance smallEtaleCompose_full [Mono j] : (smallEtaleCompose j).Full where
  map_surjective {V W} h :=
    ⟨MorphismProperty.Over.homMk h.left
      ((cancel_mono j).1 ((Category.assoc h.left W.hom j).trans (MorphismProperty.Over.w h))),
      MorphismProperty.Over.Hom.ext rfl⟩

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction along an étale morphism is a left adjoint, namely of the direct image. -/
instance etaleRestriction_isLeftAdjoint : (etaleRestriction.{u, v} j).IsLeftAdjoint :=
  (etaleDirectImageAdj.{u, v} j).isLeftAdjoint

/-- The direct image along an étale morphism is a right adjoint, namely of restriction. -/
instance etaleDirectImage_isRightAdjoint : (etaleDirectImage.{u, v} j).IsRightAdjoint :=
  (etaleDirectImageAdj.{u, v} j).isRightAdjoint

/-- Restriction along an étale morphism is also a right adjoint, namely of extension by
zero. -/
instance etaleRestriction_isRightAdjoint
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    (etaleRestriction.{u, v} j).IsRightAdjoint :=
  (extensionByZeroAdj.{u, v} j).isRightAdjoint

/-- Extension by zero is a left adjoint, namely of restriction. -/
instance extensionByZero_isLeftAdjoint
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    (extensionByZero.{u, v} j).IsLeftAdjoint :=
  (extensionByZeroAdj.{u, v} j).isLeftAdjoint

/-- Restriction along an étale morphism preserves all colimits. -/
instance etaleRestriction_preservesColimits :
    PreservesColimits (etaleRestriction.{u, v} j) :=
  (etaleDirectImageAdj.{u, v} j).leftAdjoint_preservesColimits

/-- Restriction along an étale morphism preserves all limits. -/
instance etaleRestriction_preservesLimits
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    PreservesLimits (etaleRestriction.{u, v} j) :=
  (extensionByZeroAdj.{u, v} j).rightAdjoint_preservesLimits

/-- Extension by zero preserves all colimits; in particular it is right exact. -/
instance extensionByZero_preservesColimits
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    PreservesColimits (extensionByZero.{u, v} j) :=
  (extensionByZeroAdj.{u, v} j).leftAdjoint_preservesColimits

/-- The direct image preserves all limits; in particular it is left exact. -/
instance etaleDirectImage_preservesLimits :
    PreservesLimits (etaleDirectImage.{u, v} j) :=
  (etaleDirectImageAdj.{u, v} j).rightAdjoint_preservesLimits

/-- The direct image along an étale morphism is an additive functor. -/
instance etaleDirectImage_additive : (etaleDirectImage.{u, v} j).Additive :=
  (etaleDirectImage.{u, v} j).additive_of_preserves_binary_products

/-- Restriction along an étale morphism is an additive functor. -/
instance etaleRestriction_additive : (etaleRestriction.{u, v} j).Additive :=
  (etaleDirectImageAdj.{u, v} j).left_adjoint_additive

/-- Extension by zero is an additive functor. -/
instance extensionByZero_additive
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    (extensionByZero.{u, v} j).Additive :=
  (extensionByZeroAdj.{u, v} j).left_adjoint_additive

section LeftExact

/-- The map of coproducts of abelian groups induced by a family of monomorphisms is a
monomorphism, for an index type in a universe possibly smaller than that of the groups. -/
theorem mono_sigmaMap {ι : Type w} {A B : ι → AddCommGrpCat.{max w w'}}
    (p : ∀ i, A i ⟶ B i) (hp : ∀ i, Mono (p i)) : Mono (Limits.Sigma.map p) := by
  have : AB4OfSize.{w} AddCommGrpCat.{max w w'} :=
    AB4OfSize_shrink.{w, max w w'} AddCommGrpCat.{max w w'}
  have happ : ∀ Z : Discrete ι, Mono ((Discrete.natTrans
      (F := Discrete.functor A) (G := Discrete.functor B)
      fun Z : Discrete ι => p Z.as).app Z) := fun ⟨i⟩ => hp i
  have : Mono (Discrete.natTrans (F := Discrete.functor A) (G := Discrete.functor B)
      fun Z : Discrete ι => p Z.as) := NatTrans.mono_of_mono_app _
  show Mono ((colim (J := Discrete ι) (C := AddCommGrpCat.{max w w'})).map
    (Discrete.natTrans (F := Discrete.functor A) (G := Discrete.functor B)
      fun Z : Discrete ι => p Z.as))
  infer_instance

/-- The inclusion of a summand followed by the isomorphism of the direct-sum formula is the
canonical inclusion of that summand. -/
private theorem ι_comp_sectionIso_hom
    (F : (U.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (V : X.Etale) (φ : V ⟶ smallEtaleSource j) :
    Limits.Sigma.ι
        (fun ψ : V ⟶ smallEtaleSource j => F.obj (Opposite.op (sourceDescend j ψ))) φ ≫
      (extensionByZeroPresheafSectionIso j F V).hom = extensionByZeroSummandInclusion j F φ :=
  Limits.Sigma.ι_desc (fun ψ => extensionByZeroSummandInclusion j F ψ) φ

/-- The direct-sum formula of Stacks Tag 0F4K is natural in the presheaf: the map induced on the
sections of `j_{p!}` over `V` by a map `α : F ⟶ F'` of presheaves is the coproduct of the
components of `α` at the objects `V →^φ U`. -/
theorem extensionByZeroPresheafSectionIso_naturality
    {F F' : (U.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (α : F ⟶ F') (V : X.Etale) :
    (extensionByZeroPresheafSectionIso j F V).hom ≫
        ((smallEtaleCompose j).op.lan.map α).app (Opposite.op V) =
      Limits.Sigma.map
          (f := fun φ : V ⟶ smallEtaleSource j => F.obj (Opposite.op (sourceDescend j φ)))
          (g := fun φ : V ⟶ smallEtaleSource j => F'.obj (Opposite.op (sourceDescend j φ)))
          (fun φ => α.app (Opposite.op (sourceDescend j φ))) ≫
        (extensionByZeroPresheafSectionIso j F' V).hom := by
  refine Limits.Sigma.hom_ext _ _ fun φ => ?_
  rw [reassoc_of% (ι_comp_sectionIso_hom j _ V φ), extensionByZeroSummandInclusion_naturality,
    Limits.Sigma.ι_map_assoc, ι_comp_sectionIso_hom]

/-- The map induced by a monomorphism of abelian presheaves on the sections of the left Kan
extension along composition with `j` over a scheme `V` étale over `X` is a monomorphism. -/
theorem mono_lan_map_app {F F' : (U.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (α : F ⟶ F')
    (hα : Mono α) (V : X.Etale) :
    Mono (((smallEtaleCompose j).op.lan.map α).app (Opposite.op V)) := by
  have : Mono (Limits.Sigma.map fun φ : V ⟶ smallEtaleSource j =>
      α.app (Opposite.op (sourceDescend j φ))) :=
    mono_sigmaMap.{u, max (u + 1) v} _ fun φ =>
      (NatTrans.mono_iff_mono_app α).1 hα (Opposite.op (sourceDescend j φ))
  rw [(Iso.eq_inv_comp _).2 (extensionByZeroPresheafSectionIso_naturality j α V)]
  infer_instance

/-- The left Kan extension along composition with `j` preserves monomorphisms of abelian
presheaves. -/
instance extensionByZeroPresheaf_preservesMonomorphisms :
    Functor.PreservesMonomorphisms ((smallEtaleCompose j).op.lan :
      ((U.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤
        ((X.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})) where
  preserves {_ _} α hα :=
    have happ : ∀ W, Mono (((smallEtaleCompose j).op.lan.map α).app W) := fun W =>
      mono_lan_map_app j α hα W.unop
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ happ

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- Extension by zero preserves monomorphisms. -/
instance extensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (extensionByZero.{u, v} j) := by
  change Functor.PreservesMonomorphisms
    (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
      (smallEtaleCompose j).op.lan ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  infer_instance

/-- Extension by zero preserves finite limits. -/
@[stacks 03S5 "left exactness of j_!"]
instance extensionByZero_preservesFiniteLimits
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    PreservesFiniteLimits (extensionByZero.{u, v} j) :=
  have : (extensionByZero.{u, v} j).PreservesHomology :=
    (extensionByZero.{u, v} j).preservesHomology_of_preservesMonos_and_cokernels
  (extensionByZero.{u, v} j).preservesFiniteLimits_of_preservesHomology

/-- Extension by zero along an étale morphism of schemes is an exact functor on
abelian sheaves of the small étale sites. -/
@[stacks 03S5 "j_! is an exact functor"]
theorem extensionByZero_exact
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    exactFunctor _ _ (extensionByZero.{u, v} j) :=
  have : PreservesColimitsOfSize.{0, 0} (extensionByZero.{u, v} j) :=
    (extensionByZeroAdj.{u, v} j).leftAdjoint_preservesColimits
  (exactFunctor_iff _).2
    ⟨inferInstance, PreservesColimitsOfSize.preservesFiniteColimits _⟩

end LeftExact

section Mono

variable [Mono j]

/-- For a monomorphic étale morphism `j`, the counit `j^{-1} j_* F ⟶ F` is an
isomorphism. -/
instance etaleDirectImageAdj_counit_app_isIso
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleDirectImageAdj.{u, v} j).counit.app F) := by
  have h : IsIso ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleDirectImageAdj.{u, v} j).counit.app F)) := by
    have hcounit : ((etaleDirectImageAdj.{u, v} j).counit.app F).hom =
        ((smallEtaleCompose j).op.ranAdjunction
          AddCommGrpCat.{max (u + 1) v}).counit.app F.obj :=
      Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ F
    change IsIso ((etaleDirectImageAdj.{u, v} j).counit.app F).hom
    rw [hcounit, Functor.ranAdjunction_counit]
    have happ : ∀ V, IsIso (((smallEtaleCompose j).op.ranCounit.app F.obj).app V) := fun V =>
      (Functor.isPointwiseRightKanExtensionRanCounit (smallEtaleCompose j).op F.obj
        ((smallEtaleCompose j).op.obj V)).isIso_hom_app
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  exact isIso_of_reflects_iso _ (sheafToPresheaf U.smallEtaleTopology _)

/-- For a monomorphic étale morphism, the counit of `j^{-1} ⊣ j_*` is an isomorphism of
functors. -/
instance etaleDirectImageAdj_counit_isIso : IsIso (etaleDirectImageAdj.{u, v} j).counit :=
  NatIso.isIso_of_isIso_app _

/-- For an étale monomorphism `j : U ⟶ X`, the natural isomorphism `j^{-1} j_* F ≅ F` for
abelian sheaves `F` on the small étale site of `U`, given by the counit of `j^{-1} ⊣ j_*`. -/
@[stacks 0F70 "the isomorphism j^{-1} j_* F → F"]
def directImageRestrictionIso :
    etaleDirectImage.{u, v} j ⋙ etaleRestriction.{u, v} j ≅ 𝟭 _ :=
  asIso (etaleDirectImageAdj.{u, v} j).counit

end Mono

end Stacks.EtaleCohomology

end
