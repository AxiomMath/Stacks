module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectHomotopy

/-!
# Strictly perfect approximations with no terms above a degree

Let `X` be a ringed space. This file contains the following facts about complexes of
`𝒪_X`-modules and their restrictions to open subspaces.

* Restriction to an open subspace, as the pushforward
  `AlgebraicGeometry.RingedSpace.restrictModules` to the restricted ringed space, agrees with
  restriction `SheafOfModules.overFunctor` to the slice site, and it is exact.
* Modules on an open subspace of an open subspace of `X` are modules on the corresponding open
  subspace of `X`, compatibly with restriction.
* If a strictly perfect complex `E` receives a null homotopic map which is an isomorphism in two
  consecutive degrees `a` and `a + 1`, then the degree-`a - 1` cycles of `E` are a direct summand
  of a finite free module.

## Main definitions

* `AlgebraicGeometry.RingedSpace.overToRestricted`: the equivalence
  `TopologicalSpace.Opens.sheafOfModulesEquivOver` with its codomain written as
  `StrictlyPerfect.OXMod` of the restricted ringed space.
* `AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`: restriction to an open subspace
  is `SheafOfModules.overFunctor` followed by that equivalence.
* `AlgebraicGeometry.RingedSpace.nestedModulesEquivalence`: modules on `(X|_U)|_V` are modules
  on `X|_W`, where `W` is the image of `V` in `X`.
* `AlgebraicGeometry.RingedSpace.nestedModulesCompIso`: that identification turns the composite
  of the two restrictions into the single restriction to `W`.
* `AlgebraicGeometry.RingedSpace.stupidTruncGEInclusion`: the inclusion of the stupid truncation
  in degrees `≥ a` into the complex.

## Main results

* `AlgebraicGeometry.RingedSpace.nonempty_homotopy_zero_restrictModules`: a null homotopy after
  restriction to the slice site is a null homotopy after `restrictModules`.
* `AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits` and
  `AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits`: restriction to an
  open subspace is exact.
* `AlgebraicGeometry.RingedSpace.isStrictlyPerfect_stupidTruncGE`: the stupid truncation of a
  strictly perfect complex is strictly perfect.
* `AlgebraicGeometry.RingedSpace.isDirectSummandOfFiniteFree_cycles_of_tailHomotopy`: a null
  homotopy of a map into a strictly perfect complex which is an isomorphism in two consecutive
  degrees `a`, `a + 1` makes the degree-`a - 1` cycles a direct summand of a finite free module.
* `AlgebraicGeometry.RingedSpace.isStrictlyPerfect_nestedModulesEquivalence` and
  `AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_nested`: strict
  perfection and the whole approximation statement transport along the nested identification.

## References

* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.5 (08C7)](https://stacks.math.columbia.edu/tag/08C7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
  StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-! ### Restriction to an open subspace, and its two descriptions -/

/-- Restriction of modules to the slice site over an open set preserves zero morphisms. -/
theorem overFunctor_preservesZeroMorphisms (X : RingedSpace.{u, u})
    (U : Opens X.carrier) :
    (SheafOfModules.overFunctor (structureSheafOfRings X) U :
      OXMod.{u, u} X ⥤ _).PreservesZeroMorphisms where
  map_zero _ _ := by ext V x; rfl

/-- Restriction of modules to the slice site over an open set is additive. -/
theorem overFunctor_additive (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (SheafOfModules.overFunctor (structureSheafOfRings X) U :
      OXMod.{u, u} X ⥤ _).Additive where
  map_add := by intros; ext V x; rfl

attribute [local instance] overFunctor_preservesZeroMorphisms overFunctor_additive

/-- The equivalence between modules on the slice site over `U` and modules on the restricted
ringed space, with the latter spelled as `StrictlyPerfect.OXMod` of the restricted space. -/
def overToRestricted (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.{u} ((structureSheafOfRings X).over U) ⥤
      OXMod.{u, u} (X.restrict U.isOpenEmbedding) :=
  (U.sheafOfModulesEquivOver (structureSheafOfRings X)).functor

/-- The identification of modules on the slice site with modules on the restricted space is
additive. -/
theorem overToRestricted_additive (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (overToRestricted X U).Additive where
  map_add := by
    intros
    apply (SheafOfModules.fullyFaithfulForget
      (U.sheafRestrict.obj (structureSheafOfRings X))).map_injective
    ext V z
    rfl

/-- The identification of modules on the slice site with modules on the restricted space is an
equivalence. -/
theorem overToRestricted_isEquivalence (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (overToRestricted X U).IsEquivalence :=
  inferInstanceAs ((U.sheafOfModulesEquivOver (structureSheafOfRings X)).functor).IsEquivalence

attribute [local instance] overToRestricted_additive overToRestricted_isEquivalence

/-- Restriction to an open subspace is the restriction to the slice site followed by the
identification of modules on that site with modules on the restricted space. -/
def restrictModulesIsoOverComp (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.overFunctor (structureSheafOfRings X) U ⋙ overToRestricted X U ≅
      restrictModules X U :=
  Iso.refl _

/-- A null homotopy after restriction to the slice site over `U` is a null homotopy after
`AlgebraicGeometry.RingedSpace.restrictModules` to the restricted ringed space. -/
theorem nonempty_homotopy_zero_restrictModules (U : Opens X.carrier)
    {A B : CochainComplex (OXMod.{u, u} X) ℤ} (f : A ⟶ B)
    (h : Nonempty (Homotopy
      (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) 0)) :
    Nonempty (Homotopy (((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) 0) := by
  obtain ⟨h⟩ := h
  let eC := Functor.mapHomologicalComplexCompIso (restrictModulesIsoOverComp X U)
    (ComplexShape.up ℤ)
  have hmap : Homotopy
      (((overToRestricted X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f))
      (((overToRestricted X U).mapHomologicalComplex (ComplexShape.up ℤ)).map 0) :=
    Functor.mapHomotopy _ h
  refine ⟨(Homotopy.ofEq ?_).trans
    (((hmap.compLeft (eC.inv.app A)).compRight (eC.hom.app B)).trans (Homotopy.ofEq ?_))⟩
  · have hnat := eC.hom.naturality f
    simp only [Functor.comp_map] at hnat
    rw [Category.assoc, hnat, ← Category.assoc, eC.inv_hom_id_app, Category.id_comp]
  · simp

/-- Restriction to an open subspace preserves finite colimits. -/
theorem restrictModules_preservesFiniteColimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteColimits (restrictModules.{u, u} X U) := by
  have : (SheafOfModules.overFunctor (structureSheafOfRings X) U :
      OXMod.{u, u} X ⥤ _).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward
      (𝟙 ((structureSheafOfRings X).over U))).IsLeftAdjoint
  exact preservesFiniteColimits_of_natIso (restrictModulesIsoOverComp X U)

/-- Restriction to an open subspace preserves finite limits. -/
theorem restrictModules_preservesFiniteLimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteLimits (restrictModules X U) := by
  refine ⟨fun J _ _ ↦ ⟨fun {_} ↦ ⟨fun {_} hc ↦ ?_⟩⟩⟩
  refine ⟨isLimitOfReflects
    (SheafOfModules.forget (structureSheafOfRings (X.restrict U.isOpenEmbedding))) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  exact isLimitOfPreserves (SheafOfModules.evaluation (structureSheafOfRings X)
    (Opposite.op (U.isOpenEmbedding.functor.obj V.unop))) hc

/-- A homeomorphism of spaces as an equivalence between their lattices of open sets. -/
def opensEquivalence {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    (H : α ≃ₜ β) : Opens α ≌ Opens β :=
  H.opensCongr.equivalence

/-- The equivalence of lattices of opens induced by a homeomorphism is a dense subsite for the
open-cover topologies. -/
theorem opensEquivalence_isDenseSubsite {α β : Type u}
    [TopologicalSpace α] [TopologicalSpace β] (H : α ≃ₜ β) :
    (opensEquivalence H).functor.IsDenseSubsite
      (Opens.grothendieckTopology α) (Opens.grothendieckTopology β) := by
  let e := opensEquivalence H
  refine { functorPushforward_mem_iff := ?_ }
  intro U S
  simp only [Opens.mem_grothendieckTopology]
  constructor
  · intro h x hx
    have hx' : H x ∈ e.functor.obj U := by
      change H.symm (H x) ∈ U
      simpa using hx
    obtain ⟨V, f, hf, hxV⟩ := h (H x) hx'
    rw [Sieve.mem_functorPushforward_functor] at hf
    refine ⟨e.inverse.obj V, e.inverse.map f ≫ e.unitIso.inv.app U, hf, ?_⟩
    change H x ∈ V
    exact hxV
  · intro h x hx
    have hx' : H.symm x ∈ U := by
      change x ∈ e.functor.obj U at hx
      exact hx
    obtain ⟨V, f, hf, hxV⟩ := h (H.symm x) hx'
    refine ⟨e.functor.obj V, e.functor.map f, ?_, ?_⟩
    · rw [Sieve.mem_functorPushforward_functor]
      simpa [e] using hf
    · change H.symm x ∈ V
      exact hxV

/-- An open subspace `V` of an open subspace `U` of `X` is homeomorphic to the open subspace of
`X` given by the image of `V`. -/
def nestedRestrictionHomeomorph
    (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier ≃ₜ
      (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier := by
  let f := U.inclusion'
  let hf : IsOpenEmbedding f := U.isOpenEmbedding
  let W := hf.isOpenMap.functor.obj V
  have e₀ : ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier ≃ₜ V := by
    change V ≃ₜ V
    exact Homeomorph.refl _
  have hW : (ConcreteCategory.hom f) '' V.1 = (W : Set X.carrier) := rfl
  have e₁ : V ≃ₜ W :=
    (hf.isEmbedding.homeomorphImage V.1).trans (Homeomorph.setCongr hW)
  change _ ≃ₜ W
  exact e₀.trans e₁

/-- Sending an open set of the image `W` of `V` in `X` to an open set of `X` through the doubly
restricted space and the two inclusions agrees with the inclusion of opens of `W` into opens of
`X`. -/
def nestedOpensComparison
    {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor ⋙
      V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor ≅
      (U.isOpenEmbedding.functor.obj V).isOpenEmbedding.functor := by
  let H := nestedRestrictionHomeomorph X U V
  refine NatIso.ofComponents (fun A ↦ eqToIso ?_)
  ext x
  change (∃ y : U, (∃ z : V, H z ∈ A ∧ z.val = y) ∧ y.val = x) ↔
    ∃ z : U.isOpenEmbedding.functor.obj V, z ∈ A ∧ z.val = x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨H z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(H.symm z).val, ⟨H.symm z, ?_, rfl⟩, ?_⟩
    · have h : H (H.symm z) = z := H.apply_symm_apply z
      exact (congrArg (fun t ↦ t ∈ A) h).mpr hz
    exact congrArg Subtype.val (H.apply_symm_apply z)

/-- The functor on opens induced by the inclusion of an open subspace is continuous, stated with
the site of the subspace spelled through `SheafedSpace.restrict`. -/
theorem restrictFunctor_isContinuous (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  U.isOpenEmbedding.functor_isContinuous

attribute [local instance] restrictFunctor_isContinuous

/-- Taking the image in `X` of an open set of an open subspace of an open subspace is
continuous. -/
theorem nestedFunctor_isContinuous (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ V.isOpenEmbedding.functor U.isOpenEmbedding.functor
    (Opens.grothendieckTopology
      ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology X.carrier)
    (restrictFunctor_isContinuous (X.restrict U.isOpenEmbedding) V)
    (restrictFunctor_isContinuous X U)

attribute [local instance] nestedFunctor_isContinuous

/-- The comparison of the two descriptions of an open subspace of an open subspace is a dense
subsite. -/
theorem nestedOpensEquivalence_isDenseSubsite (X : RingedSpace.{u, u})
    (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor.IsDenseSubsite
      (Opens.grothendieckTopology
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
      (Opens.grothendieckTopology
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier) :=
  opensEquivalence_isDenseSubsite (nestedRestrictionHomeomorph X U V).symm

/-- The inverse comparison is a dense subsite as well. -/
theorem nestedOpensEquivalence_inverse_isDenseSubsite (X : RingedSpace.{u, u})
    (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (opensEquivalence (nestedRestrictionHomeomorph X U V).symm).inverse.IsDenseSubsite
      (Opens.grothendieckTopology
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier) :=
  opensEquivalence_isDenseSubsite (nestedRestrictionHomeomorph X U V)

attribute [local instance] nestedOpensEquivalence_isDenseSubsite
  nestedOpensEquivalence_inverse_isDenseSubsite

/-- The composite of the comparison with the image functor is continuous. -/
theorem nestedComparison_isContinuous (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    ((opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor ⋙
      V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  @Functor.isContinuous_comp _ _ _ _ _ _
    (opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor
    (V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor)
    (Opens.grothendieckTopology
      (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
    (Opens.grothendieckTopology
      ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology X.carrier)
    inferInstance (nestedFunctor_isContinuous X U V)

attribute [local instance] nestedComparison_isContinuous



/-- Modules on an open subspace of an open subspace of `X` are the same as modules on the
corresponding open subspace of `X`. -/
def nestedModulesEquivalence {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ≌
      OXMod.{u, u} (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) := by
  let E := opensEquivalence (nestedRestrictionHomeomorph X U V).symm
  let F := V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor
  let G := (U.isOpenEmbedding.functor.obj V).isOpenEmbedding.functor
  let c : E.functor ⋙ F ≅ G := nestedOpensComparison U V
  let b : E.inverse ⋙ G ≅ F :=
    Functor.isoWhiskerLeft E.inverse c.symm ≪≫
      (Functor.associator E.inverse E.functor F).symm ≪≫
      Functor.isoWhiskerRight E.counitIso F ≪≫ F.leftUnitor
  let O := (structureSheafOfRings X).obj
  let φ : structureSheafOfRings
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) ⟶
      (E.functor.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).obj
        (structureSheafOfRings
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) :=
    (ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op c) O)).hom
  let ψ : structureSheafOfRings
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ⟶
      (E.inverse.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).obj
        (structureSheafOfRings
          (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)) :=
    (ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op b) O)).hom
  refine SheafOfModules.pushforwardPushforwardEquivalence E φ ψ ?_ ?_
  · ext A : 2
    change O.map _ = O.map _ ≫ O.map _
    rw [← O.map_comp]
    congr 1
  · ext A : 2
    change O.map _ ≫ O.map _ ≫ O.map _ = 𝟙 _
    rw [← O.map_comp, ← O.map_comp, ← O.map_id]
    congr 1


/-- Restricting to `U` and then to an open `V` of `U` is, up to the identification of modules
on the doubly restricted space with modules on the corresponding open of `X`, the same as
restricting to that open of `X` in one step. -/
def nestedModulesCompIso {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) V) ⋙
        (nestedModulesEquivalence U V).functor ≅
      restrictModules X (U.isOpenEmbedding.functor.obj V) := by
  let ψ : structureSheafOfRings
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) ⟶
      (((opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor ⋙
        V.isOpenEmbedding.functor ⋙
          U.isOpenEmbedding.functor).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology
          (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafOfRings X) :=
    (ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (nestedOpensComparison U V)) (structureSheafOfRings X).obj)).hom
  let e := @SheafOfModules.pushforwardCongr₂ _ _ _ _ _ _ _ _ _ _
    (nestedComparison_isContinuous X U V)
    (restrictFunctor_isContinuous X (U.isOpenEmbedding.functor.obj V))
    (𝟙 (structureSheafOfRings
      (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)))
    ψ (nestedOpensComparison U V) (by ext : 2; rfl)
  let a : structureSheafOfRings (X.restrict U.isOpenEmbedding) ⟶
      (U.isOpenEmbedding.functor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafOfRings X) := 𝟙 _
  let b : structureSheafOfRings
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ⟶
      (V.isOpenEmbedding.functor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)).obj
        (structureSheafOfRings (X.restrict U.isOpenEmbedding)) := 𝟙 _
  let φ : structureSheafOfRings
        (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) ⟶
      ((opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor
          ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology
          (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding).carrier)
        (Opens.grothendieckTopology
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
        |>.obj (structureSheafOfRings
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) :=
    (ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (nestedOpensComparison U V)) (structureSheafOfRings X).obj)).hom
  let δ : structureSheafOfRings
        ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) ⟶
      (@Functor.sheafPushforwardContinuous _ _ _ _
        (V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor) RingCat.{u} _
        (Opens.grothendieckTopology
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology X.carrier)
        (nestedFunctor_isContinuous X U V)).obj (structureSheafOfRings X) := 𝟙 _
  let e₁' : restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) V ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ _ _ _ _ _
        (nestedFunctor_isContinuous X U V) δ :=
    @SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _
        (restrictFunctor_isContinuous (X.restrict U.isOpenEmbedding) V) b _ _ _
        (restrictFunctor_isContinuous X U) a ≪≫
      SheafOfModules.pushforwardCongr (by ext : 2; rfl)
  refine Functor.isoWhiskerRight e₁' (SheafOfModules.pushforward φ) ≪≫
    @SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _
        (opensEquivalence (nestedRestrictionHomeomorph X U V).symm).functor _ _
        inferInstance φ _ (V.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor) _
        (nestedFunctor_isContinuous X U V) δ ≪≫ ?_
  refine SheafOfModules.pushforwardCongr ?_ ≪≫ e.symm
  ext A x
  rfl


/-! ### Stupid truncation above a degree -/

/-- The inclusion of the stupid truncation in degrees `≥ a` into the complex: the identity in
degrees `≥ a` and zero below. -/
def stupidTruncGEInclusion {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] (E : CochainComplex C ℤ) (a : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE a) ⟶ E := by
  let e := ComplexShape.embeddingUpIntGE a
  let T := (E.restriction e).extend e
  let f (i : ℤ) : T.X i ⟶ E.X i := by
    by_cases hi : a ≤ i
    · have hm : e.f ((i - a).toNat) = i := by
        rw [ComplexShape.embeddingUpIntGE_f]
        omega
      exact ((E.restriction e).extendXIso e hm).hom ≫ (E.restrictionXIso e hm).hom
    · exact 0
  apply CochainComplex.ofHom f
  intro i
  by_cases hi : a ≤ i
  · have hj : a ≤ i + 1 := by omega
    have hmi : e.f ((i - a).toNat) = i := by
      rw [ComplexShape.embeddingUpIntGE_f]
      omega
    have hmj : e.f ((i + 1 - a).toNat) = i + 1 := by
      rw [ComplexShape.embeddingUpIntGE_f]
      omega
    have hTd : T.d i (i + 1) =
        ((E.restriction e).extendXIso e hmi).hom ≫ (E.restrictionXIso e hmi).hom ≫
          E.d i (i + 1) ≫ (E.restrictionXIso e hmj).inv ≫
            ((E.restriction e).extendXIso e hmj).inv := by
      change ((E.restriction e).extend e).d i (i + 1) = _
      rw [HomologicalComplex.extend_d_eq (K := E.restriction e) (e := e) hmi hmj,
        HomologicalComplex.restriction_d_eq (K := E) (e := e)
        (i := (i - a).toNat) (j := (i + 1 - a).toNat) hmi hmj]
      simp [Category.assoc]
    simp only [f, dite_eq_left hi, dite_eq_left hj]
    rw [hTd]
    simp [Category.assoc]
  · have hz : IsZero (T.X i) := by
      apply E.isZero_stupidTrunc_X e i
      intro n
      rw [ComplexShape.embeddingUpIntGE_f]
      omega
    have hzd : T.d i (i + 1) = 0 := hz.eq_of_src _ _
    simp [f, hi, hzd]

/-- The stupid truncation of a strictly perfect complex in degrees `≥ a` is strictly
perfect. -/
theorem isStrictlyPerfect_stupidTruncGE
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (hE : IsStrictlyPerfect E) (a : ℤ) :
    IsStrictlyPerfect (E.stupidTrunc (ComplexShape.embeddingUpIntGE a)) := by
  let e := ComplexShape.embeddingUpIntGE a
  have hcases (i : ℤ) :
      IsZero ((E.stupidTrunc e).X i) ∨ Nonempty ((E.stupidTrunc e).X i ≅ E.X i) := by
    by_cases him : ∃ j : ℕ, e.f j = i
    · obtain ⟨j, hji⟩ := him
      exact .inr ⟨E.stupidTruncXIso e hji⟩
    · exact .inl (E.isZero_stupidTrunc_X e i (by simpa using him))
  constructor
  · refine hE.bounded.subset fun i hi hEi ↦ ?_
    rcases hcases i with hz | ⟨⟨φ⟩⟩
    · exact hi hz
    · exact hi (hEi.of_iso φ)
  · intro i
    rcases hcases i with hz | ⟨⟨φ⟩⟩
    · exact isDirectSummandOfFiniteFree_of_isZero hz
    · exact isDirectSummandOfFiniteFree_of_iso φ (hE.directSummand i)

/-! ### The degree-`r` cycles from a local null homotopy -/

/-- The kernel of a split epimorphism out of a direct summand of a finite free module is
again a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_kernel_of_split
    {A B : OXMod.{u, u} X} (f : A ⟶ B) (s : B ⟶ A) (hs : s ≫ f = 𝟙 B)
    (hA : IsDirectSummandOfFiniteFree A) : IsDirectSummandOfFiniteFree (kernel f) := by
  let p : A ⟶ A := 𝟙 A - f ≫ s
  have hp : p ≫ f = 0 := by simp [p, Category.assoc, hs]
  exact isDirectSummandOfFiniteFree_of_retract
    { i := kernel.ι f
      r := kernel.lift f p hp
      retract := by
        apply (cancel_mono (kernel.ι f)).1
        simp only [Category.assoc, kernel.lift_ι]
        simp [p] } hA

/-- If a strictly perfect complex `E` receives a map `ι` from a complex `T`, null homotopic,
with `ι` an isomorphism in degrees `a` and `a + 1`, then the degree-`a - 1` cycles of `E` are
a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_cycles_of_tailHomotopy
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (hE : IsStrictlyPerfect E) (a : ℤ)
    (T : CochainComplex (OXMod.{u, u} X) ℤ) (ι : T ⟶ E)
    (hia : IsIso (ι.f a)) (hia1 : IsIso (ι.f (a + 1))) (h : Homotopy ι 0) :
    IsDirectSummandOfFiniteFree (E.cycles (a - 1)) := by
  have hnext : (ComplexShape.up ℤ).next (a - 1) = a := by
    rw [CochainComplex.next]; omega
  let e₀ : T.X a ≅ E.X a := asIso (ι.f a)
  let e₁ : T.X (a + 1) ≅ E.X (a + 1) := asIso (ι.f (a + 1))
  have hcomm : ι.f a =
      T.d a (a + 1) ≫ h.hom (a + 1) a + h.hom a (a - 1) ≫ E.d (a - 1) a := by
    have hh := h.comm a
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel a (a + 1) by simp),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (a - 1) a by simp)] at hh
    simpa using hh
  have hchain : e₀.inv ≫ T.d a (a + 1) = E.d a (a + 1) ≫ e₁.inv := by
    apply (cancel_mono e₁.hom).1
    have hc := ι.comm a (a + 1)
    calc
      e₀.inv ≫ T.d a (a + 1) ≫ e₁.hom = e₀.inv ≫ T.d a (a + 1) ≫ ι.f (a + 1) := rfl
      _ = e₀.inv ≫ ι.f a ≫ E.d a (a + 1) := by rw [← hc]
      _ = E.d a (a + 1) := by simp [e₀]
      _ = E.d a (a + 1) ≫ e₁.inv ≫ e₁.hom := by simp [e₁]
  have hz : E.iCycles a ≫ e₀.inv ≫ T.d a (a + 1) ≫ h.hom (a + 1) a = 0 := by
    have hz₀ : E.iCycles a ≫ e₀.inv ≫ T.d a (a + 1) = 0 := by
      rw [hchain, ← Category.assoc, E.iCycles_d a (a + 1), Limits.zero_comp]
    simpa using congrArg (fun f ↦ f ≫ h.hom (a + 1) a) hz₀
  have hs : (E.iCycles a ≫ e₀.inv ≫ h.hom a (a - 1)) ≫ E.toCycles (a - 1) a =
      𝟙 (E.cycles a) := by
    apply (cancel_mono (E.iCycles a)).1
    rw [Category.assoc, E.toCycles_i, Category.id_comp]
    have hsplit : h.hom a (a - 1) ≫ E.d (a - 1) a =
        e₀.hom - T.d a (a + 1) ≫ h.hom (a + 1) a := by
      refine eq_sub_iff_add_eq.mpr ?_
      rw [show e₀.hom = ι.f a from rfl, hcomm, add_comm]
    calc
      (E.iCycles a ≫ e₀.inv ≫ h.hom a (a - 1)) ≫ E.d (a - 1) a =
          E.iCycles a ≫ e₀.inv ≫ (e₀.hom - T.d a (a + 1) ≫ h.hom (a + 1) a) := by
        rw [Category.assoc, Category.assoc, hsplit]
      _ = (E.iCycles a ≫ e₀.inv ≫ e₀.hom) -
          E.iCycles a ≫ e₀.inv ≫ T.d a (a + 1) ≫ h.hom (a + 1) a := by
        simp only [Preadditive.comp_sub]
      _ = E.iCycles a := by
        rw [hz]
        simp [e₀]
  have hker : IsDirectSummandOfFiniteFree (kernel (E.toCycles (a - 1) a)) :=
    isDirectSummandOfFiniteFree_kernel_of_split _ _ hs (hE.directSummand (a - 1))
  refine isDirectSummandOfFiniteFree_of_iso ?_ hker
  refine (IsLimit.conePointUniqueUpToIso (E.cyclesIsKernel (a - 1) a hnext)
    (kernelIsKernel (E.d (a - 1) a))) ≪≫ ?_
  exact kernelIsoOfEq (E.toCycles_i (a - 1) a).symm ≪≫
    kernelCompMono (E.toCycles (a - 1) a) (E.iCycles a)

/-! ### Exact functors and maps on cohomology -/

/-- An exact additive functor carries a map which is an isomorphism on cohomology in a degree to
a map which is an isomorphism on cohomology in that degree. -/
theorem isIso_homologyMap_map {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {E G : CochainComplex A ℤ} (f : E ⟶ G) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap f j)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) j) := by
  have : QuasiIsoAt f j := (quasiIsoAt_iff_isIso_homologyMap _ _).2 h
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- An exact additive functor carries a map which is an epimorphism on cohomology in a degree to
a map which is an epimorphism on cohomology in that degree. -/
theorem epi_homologyMap_map {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex A ℤ} (α : P ⟶ Q) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap α j)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) j) := by
  have hFα : Epi (F.map (HomologicalComplex.homologyMap α j)) := F.map_epi _
  have hn : F.map (HomologicalComplex.homologyMap α j) ≫ ((Q.sc j).mapHomologyIso F).inv =
      ((P.sc j).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) j :=
    ShortComplex.mapHomologyIso_inv_naturality
      (φ := (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) j).map α) F
  have hinv : Epi ((Q.sc j).mapHomologyIso F).inv :=
    IsIso.epi_of_iso ((Q.sc j).mapHomologyIso F).inv
  have hfac : Epi (F.map (HomologicalComplex.homologyMap α j) ≫
      ((Q.sc j).mapHomologyIso F).inv) :=
    @epi_comp _ _ _ _ _ (F.map (HomologicalComplex.homologyMap α j)) hFα
      ((Q.sc j).mapHomologyIso F).inv hinv
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hfac hn.symm


/-! ### Transporting strict perfection along the nested identification -/

/-- The pushforward of the unit module along an isomorphism of sheaves of rings is the unit
module. -/
def pushforwardUnitIso {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u} φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  let f := SheafOfModules.unitToPushforwardObjUnit φ
  have hforget : IsIso ((SheafOfModules.forget S ⋙
      PresheafOfModules.toPresheaf S.obj).map f) := by
    change IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat AddCommGrpCat))
    infer_instance
  have hf : IsIso f :=
    isIso_of_reflects_iso f (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj)
  exact (asIso f).symm

/-- The nested identification is additive. -/
theorem nestedModulesEquivalence_functor_additive {X : RingedSpace.{u, u}}
    (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (nestedModulesEquivalence U V).functor.Additive where
  map_add := by intros; ext W x; rfl

attribute [local instance 10] nestedModulesEquivalence_functor_additive

/-- The nested identification sends the structure sheaf to the structure sheaf. -/
def nestedStructureIso {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (nestedModulesEquivalence U V).functor.obj
        (structureModule ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ≅
      structureModule (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) := by
  apply pushforwardUnitIso

/-- The nested identification preserves being a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_nestedModulesEquivalence
    {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    {A : OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)}
    (hA : IsDirectSummandOfFiniteFree A) :
    IsDirectSummandOfFiniteFree ((nestedModulesEquivalence U V).functor.obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := hA
  have h1 : Retract ((nestedModulesEquivalence U V).functor.obj
        (finiteFree ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding) n))
      (finiteFree (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding) n) :=
    ((nestedModulesEquivalence U V).functor.retractMapBiproduct
        fun _ : Fin n ↦ structureModule
          ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)).trans
      (Limits.biproduct.mapIso (fun _ : Fin n ↦ nestedStructureIso U V)).retract
  exact ⟨n, ⟨(ρ.map (nestedModulesEquivalence U V).functor).trans
    (h1.map (moduleULift
      (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)))⟩⟩

/-- The nested identification preserves strict perfection. -/
theorem isStrictlyPerfect_nestedModulesEquivalence {X : RingedSpace.{u, u}}
    (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (P : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect ((((nestedModulesEquivalence U V).functor).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hz ↦
    hi ((nestedModulesEquivalence U V).functor.isZero_obj hz)
  directSummand i :=
    isDirectSummandOfFiniteFree_nestedModulesEquivalence U V (hP.directSummand i)

/-- Restricting a complex to `U` and then to `V` is, under the nested identification, the
restriction to the corresponding open of `X`. -/
def nestedComplexIso {X : RingedSpace.{u, u}} (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (C : CochainComplex (OXMod.{u, u} X) ℤ) :
    (((nestedModulesEquivalence U V).functor).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictComplex (restrictComplex C U) V) ≅
      restrictComplex C (U.isOpenEmbedding.functor.obj V) :=
  (NatIso.mapHomologicalComplex (nestedModulesCompIso U V) (ComplexShape.up ℤ)).app C


/-! ### Transporting an approximation along the nested identification -/

/-- Transporting a truncated approximation on an open subspace of an open subspace of `X` to
the corresponding open subspace of `X`. -/
theorem exists_strictlyPerfect_approximation_of_nested
    (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier)
    (C : CochainComplex (OXMod.{u, u} X) ℤ) (m r : ℤ)
    (Q : CochainComplex
      (OXMod.{u, u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) ℤ)
    (hQ : IsStrictlyPerfect Q) (hQtop : ∀ i : ℤ, r < i → IsZero (Q.X i))
    (β : Q ⟶ restrictComplex (restrictComplex C U) V)
    (hβiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap β i))
    (hβepi : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ P : CochainComplex
        (OXMod.{u, u} (X.restrict (U.isOpenEmbedding.functor.obj V).isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧ (∀ i : ℤ, r < i → IsZero (P.X i)) ∧
      ∃ α : P ⟶ restrictComplex C (U.isOpenEmbedding.functor.obj V),
        (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
        Epi (HomologicalComplex.homologyMap α m) := by
  refine ⟨(((nestedModulesEquivalence U V).functor).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q,
    isStrictlyPerfect_nestedModulesEquivalence U V Q hQ, ?_,
    (((nestedModulesEquivalence U V).functor).mapHomologicalComplex
      (ComplexShape.up ℤ)).map β ≫ (nestedComplexIso U V C).hom, ?_, ?_⟩
  · exact fun i hi ↦ (nestedModulesEquivalence U V).functor.isZero_obj (hQtop i hi)
  · intro i hmi
    rw [HomologicalComplex.homologyMap_comp]
    have hβi := isIso_homologyMap_map (nestedModulesEquivalence U V).functor β i (hβiso i hmi)
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have hβm := epi_homologyMap_map (nestedModulesEquivalence U V).functor β m hβepi
    have hem : Epi (HomologicalComplex.homologyMap (nestedComplexIso U V C).hom m) :=
      inferInstance
    exact @epi_comp _ _ _ _ _ _ hβm _ hem

end AlgebraicGeometry.RingedSpace

end
