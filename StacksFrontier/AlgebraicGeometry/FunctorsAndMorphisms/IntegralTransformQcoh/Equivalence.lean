module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.RingActions
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.RightExact
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.DerivedCoherent.SerreClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent kernels and right exact linear functors

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R` with `X` **affine**.
A quasi-coherent module `K` on `X ×_R Y` has an integral transform
`F ↦ pr_{2,*}(pr_1^* F ⊗ K)` from quasi-coherent modules on `X` to quasi-coherent modules on
`Y`, which is `R`-linear, right exact and commutes with arbitrary direct sums.  This file makes
that assignment a functor of the kernel and shows that it is an equivalence of categories.

## Main definitions

* `AlgebraicGeometry.integralTransformQcohFunctor` is the integral transform of a quasi-coherent
  kernel, as a functor of the kernel.
* `AlgebraicGeometry.integralTransformQcohFunctorLift` restricts its codomain to the full
  subcategory `AlgebraicGeometry.rightExactLinearCoproductFunctor` of the functors that are
  `R`-linear, right exact and commute with arbitrary direct sums.
* `AlgebraicGeometry.integralTransformQcohEquivalence` is that lift, as an equivalence of
  categories.

## Main results

* `AlgebraicGeometry.integralTransformQcohFunctorComparison`: after forgetting quasi-coherence
  of the values, the kernel-functorial integral transform is the pullback--tensor--pushforward
  formula, naturally in the kernel.
* `AlgebraicGeometry.integralTransformQcohFunctorLift_obj_obj`: the functor sends a kernel to
  its integral transform.
* `AlgebraicGeometry.faithful_integralTransformQcohFunctorLift`,
  `AlgebraicGeometry.full_integralTransformQcohFunctorLift` and
  `AlgebraicGeometry.essSurj_integralTransformQcohFunctorLift`: that functor is faithful, full
  and essentially surjective.
* `AlgebraicGeometry.integralTransformQcohEquivalence_functor_obj_obj`: the equivalence sends a
  kernel to its integral transform.

## Implementation notes

`R`-linearity is `CategoryTheory.Functor.Additive` together with
`CategoryTheory.Functor.Linear R` for the linear structure `AlgebraicGeometry.modulesLinear`
induced by the structure morphism to `Spec R`; right exactness is
`CategoryTheory.Limits.PreservesFiniteColimits`; and commuting with arbitrary direct sums is
preservation of colimits of discrete diagrams indexed by every type in the universe of the
modules.  That the integral transform satisfies all three is
`AlgebraicGeometry.rightExactLinearCoproductFunctor_quasicoherentIntegralTransform`.

Functoriality in the kernel is obtained by lifting the pullback--tensor--pushforward formula,
which is functorial in the kernel because the sheaf tensor product is a bifunctor, through the
inclusion of the quasi-coherent modules; that inclusion is fully faithful, so the lift is
determined on morphisms by the comparison isomorphisms of Tag 0FZB.

Faithfulness reduces to the value of the functor on the structure sheaf.  The value of the
integral transform of `K` there is `pr_{2,*}K` (`integralTransformUnitIso`), a natural
transformation out of a right exact, coproduct-preserving functor on the quasi-coherent modules
of an affine scheme is determined by its value on the structure sheaf (`affineNatTrans_ext`,
which rests on the equivalence between modules over `Γ(X, ⊤)` and quasi-coherent modules on `X`
and on Tag 0GNQ), and direct image along the affine morphism `pr_2` is an equivalence onto the
quasi-coherent `pr_{2,*}𝒪_{X ×_R Y}`-modules by Tag 01SB.

Fullness reduces to the structure sheaf in the same way.  The value there of a natural
transformation of integral transforms is a morphism of direct images along `pr_2` commuting
with the action of `Γ(X, ⊤)`; over an affine open of `Y` the sections of
`pr_{2,*}𝒪_{X ×_R Y}` are a pushout of the sections of `𝒪_Y` and the global functions of `X`
over those of `Spec R`, so such a morphism is automatically linear over that sheaf of rings
(`affine_pushforward_map_smul`) and Tag 01SB returns a morphism of kernels inducing it.

Essential surjectivity runs the same argument backwards.  The value of a right exact,
coproduct-preserving functor on the structure sheaf carries an action of `Γ(X, ⊤)` extending
the base action (`valueAction`), which `exists_pushforwardModule_of_sectionAction` descends to
a module over `pr_{2,*}𝒪_{X ×_R Y}`, again because those sections are a pushout of rings.  By
Tag 01SB that module is the direct image of a quasi-coherent kernel, and
`affineFunctorIsoOfUnitIso` upgrades the resulting equivariant isomorphism of values on the
structure sheaf to an isomorphism of functors.

The elaborator is kept away from the large concrete terms involved: `fullPreimageHom` is made
irreducible, and the morphism identities are assembled from `congrArg` and `Eq.trans` over
small intermediate terms rather than by rewriting inside them.

## References

* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0GNQ](https://stacks.math.columbia.edu/tag/0GNQ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.IntegralTransformQcoh

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open scoped IsMulCommutative

/-- A functor lifted along a fully faithful functor `G` from a prescribed assignment on
objects together with isomorphisms identifying the values of `G` on it with those of `F`. -/
noncomputable def liftFunctorAlongFullyFaithful
    {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (G : D ⥤ E) (hG : G.FullyFaithful) (obj : C → D)
    (e : ∀ X, G.obj (obj X) ≅ F.obj X) : C ⥤ D where
  obj := obj
  map {X Y} f := hG.preimage ((e X).hom ≫ F.map f ≫ (e Y).inv)
  map_id X := hG.map_injective (by simp)
  map_comp f g := hG.map_injective (by simp [Category.assoc])

/-- Composing the lift along a fully faithful functor with that functor recovers the functor
it was lifted from, by the given isomorphisms. -/
noncomputable def liftFunctorAlongFullyFaithfulIso
    {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (G : D ⥤ E) (hG : G.FullyFaithful) (obj : C → D)
    (e : ∀ X, G.obj (obj X) ≅ F.obj X) :
    liftFunctorAlongFullyFaithful F G hG obj e ⋙ G ≅ F :=
  NatIso.ofComponents e (by
    intro X Y f
    dsimp only [liftFunctorAlongFullyFaithful, Functor.comp_map]
    rw [hG.map_preimage]
    simp)

/-- The pullback--tensor--pushforward formula of Tag 0FZC, as a functor of the kernel as well
as of the module it is applied to. -/
noncomputable def formulaFunctor (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) :
    (pullback X.hom Y.hom).Modules ⥤
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        Y.left.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩ ⋙
    (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ⋙
    (Functor.whiskeringLeft _ _ _).obj ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (pullback.fst X.hom Y.hom))

/-- At a fixed kernel, the kernel-functorial formula is the formula of Tag 0FZC. -/
noncomputable def formulaFunctorObjIso
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    (K : (pullback X.hom Y.hom).Modules) :
    (formulaFunctor R X Y).obj K ≅ AlgebraicGeometry.integralTransformFormula R X Y K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    simp only [Iso.refl_hom]
    rfl)

/-- The integral transform attached to a quasi-coherent kernel, compared with the
kernel-functorial formula after forgetting quasi-coherence of its values. -/
noncomputable def comparisonData
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    ((Functor.whiskeringRight _ _ _).obj
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι).obj
      (quasicoherentIntegralTransform R X Y K) ≅
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K :=
  (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
    (formulaFunctorObjIso R X Y K.obj).symm

/-- Morphisms of quasi-coherent modules with affine source are determined by their direct
images, direct image along an affine morphism being an equivalence onto the quasi-coherent
modules over the direct image of the structure sheaf. -/
private lemma pushforward_map_injective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f]
    {K L : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    {a b : K ⟶ L}
    (h : (Scheme.Modules.pushforward f).map a.hom =
      (Scheme.Modules.pushforward f).map b.hom) : a = b := by
  let F := Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward f
  have : F.IsEquivalence :=
    Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward f
  apply F.map_injective
  apply ObjectProperty.hom_ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  exact congrArg (fun k => (k.val.app U).hom x) h

/-- Direct image of modules along a morphism of schemes is direct image over the direct image
of the structure sheaf followed by restriction of scalars. -/
private lemma pushforward_map_eq_restrictScalars_map
    {X S : Scheme.{u}} (f : X ⟶ S) {M N : X.Modules} (g : M ⟶ N) :
    (Scheme.Modules.pushforward f).map g =
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).map
        ((pushforwardModules f.base X.ringCatSheaf).map g) := rfl

/-- The global functions of the target of a morphism of schemes, as a constant presheaf,
mapping to the structure presheaf of the source. -/
private noncomputable def constantToStructure {X S : Scheme.{u}} (f : X ⟶ S) :
    (Functor.const X.Opensᵒᵖ).obj Γ(S, ⊤) ⟶ X.presheaf where
  app U := f.appLE ⊤ U.unop (le_top.trans (le_of_eq f.preimage_top.symm))
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp]
    exact (Scheme.Hom.appLE_map f (le_top.trans (le_of_eq f.preimage_top.symm)) i).symm

/-- The global functions of `X`, as a constant presheaf on `Y`, mapping to the direct image
along the second projection of the structure presheaf of `X ×_R Y`. -/
private noncomputable def constantToProduct (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) :
    (Functor.const Y.left.Opensᵒᵖ).obj Γ(X.left, ⊤) ⟶
      (Opens.map (pullback.snd X.hom Y.hom).base).op ⋙
        (pullback X.hom Y.hom).presheaf where
  app U := (pullback.fst X.hom Y.hom).appLE ⊤
    ((pullback.snd X.hom Y.hom) ⁻¹ᵁ U.unop)
    (le_top.trans (le_of_eq (pullback.fst X.hom Y.hom).preimage_top.symm))
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp]
    exact (Scheme.Hom.appLE_map (pullback.fst X.hom Y.hom)
      (le_top.trans (le_of_eq (pullback.fst X.hom Y.hom).preimage_top.symm))
      ((Opens.map (pullback.snd X.hom Y.hom).base).op.map i)).symm

/-- The two routes from the global functions of `Spec R` to the direct image of the structure
presheaf of `X ×_R Y` along the second projection agree. -/
private lemma productStructureSquare (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) :
    (Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop ≫ constantToProduct R X Y =
      constantToStructure Y.hom ≫ (pullback.snd X.hom Y.hom).c := by
  apply NatTrans.ext
  funext U
  show X.hom.appTop ≫ (pullback.fst X.hom Y.hom).appLE ⊤
      ((pullback.snd X.hom Y.hom) ⁻¹ᵁ U.unop) _ =
    Y.hom.appLE ⊤ U.unop _ ≫ (pullback.snd X.hom Y.hom).app U.unop
  rw [Scheme.Hom.app_eq_appLE (pullback.snd X.hom Y.hom), Scheme.Hom.appLE_comp_appLE,
    show X.hom.appTop =
        X.hom.appLE ⊤ ⊤ (le_top.trans (le_of_eq X.hom.preimage_top.symm)) from
      (Scheme.Hom.appLE_eq_app X.hom).symm,
    Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact pullback.condition

/-- The comparison from the pushout of presheaves of rings on `Y` to the direct image of the
structure presheaf of `X ×_R Y` along the second projection. -/
private noncomputable def productStructurePresheafMap (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) :
    pushout ((Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop)
        (constantToStructure Y.hom) ⟶
      (Opens.map (pullback.snd X.hom Y.hom).base).op ⋙
        (pullback X.hom Y.hom).presheaf :=
  pushout.desc (constantToProduct R X Y) (pullback.snd X.hom Y.hom).c
    (productStructureSquare R X Y)

/-- On an affine open of `Y`, the comparison from the pushout of presheaves of rings is an
isomorphism, the sections over it forming a pushout square of rings. -/
private lemma productStructurePresheafMap_isIso_app (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsIso ((productStructurePresheafMap R X Y).app (.op U)) := by
  let H := IsPullback.of_hasPullback X.hom Y.hom
  have hi := isIso_pushoutSection_of_isAffineOpen H
    (US := ⊤) (UT := U) (UX := ⊤)
    (le_top.trans (le_of_eq Y.hom.preimage_top.symm))
    (le_top.trans (le_of_eq X.hom.preimage_top.symm))
    (UY := (pullback.snd X.hom Y.hom) ⁻¹ᵁ U) (by simp)
    (isAffineOpen_top (Spec (.of R))) hU (isAffineOpen_top X.left)
  have hp := (isIso_pushoutSection_iff H
    (US := ⊤) (UT := U) (UX := ⊤)
    (le_top.trans (le_of_eq Y.hom.preimage_top.symm))
    (le_top.trans (le_of_eq X.hom.preimage_top.symm))
    (UY := (pullback.snd X.hom Y.hom) ⁻¹ᵁ U) (by simp)).mp hi
  rw [show X.hom.appLE ⊤ ⊤ (le_top.trans (le_of_eq X.hom.preimage_top.symm)) =
    X.hom.appTop from Scheme.Hom.appLE_eq_app X.hom] at hp
  let hq := (IsPushout.of_hasPushout
    ((Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop)
    (constantToStructure Y.hom)).map ((evaluation _ _).obj (.op U))
  let e := hq.isoIsPushout _ _ hp
  have he : (productStructurePresheafMap R X Y).app (.op U) = e.hom := by
    apply hq.hom_ext
    · exact (congrArg (fun a => a.app (.op U))
        (pushout.inl_desc (constantToProduct R X Y) (pullback.snd X.hom Y.hom).c
          (productStructureSquare R X Y))).trans
        (hq.inl_isoIsPushout_hom _ _ hp).symm
    · exact ((congrArg (fun a => a.app (.op U))
        (pushout.inr_desc (constantToProduct R X Y) (pullback.snd X.hom Y.hom).c
          (productStructureSquare R X Y))).trans
        (Scheme.Hom.app_eq_appLE (pullback.snd X.hom Y.hom))).trans
        (hq.inr_isoIsPushout_hom _ _ hp).symm
  rw [he]
  infer_instance

/-- The comparison from the pushout of presheaves of rings is locally bijective: the affine
opens form a basis, and on each of them it is an isomorphism. -/
private lemma productStructurePresheafMap_locallyBijective (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    let α := Functor.whiskerRight (productStructurePresheafMap R X Y)
      (forget₂ CommRingCat RingCat)
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y.left) α ∧
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.left) α := by
  dsimp only
  let α := Functor.whiskerRight (productStructurePresheafMap R X Y)
    (forget₂ CommRingCat RingCat)
  have hi (U : Y.left.Opens) (hU : IsAffineOpen U) : IsIso (α.app (.op U)) := by
    have := productStructurePresheafMap_isIso_app R X Y U hU
    exact Functor.map_isIso (forget₂ CommRingCat RingCat) _
  constructor
  · constructor
    rintro ⟨U⟩ x y h p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    refine ⟨V, homOfLE hVU, ?_, hpV⟩
    have := hi V hV
    apply (ConcreteCategory.bijective_of_isIso (α.app (.op V))).1
    exact (NatTrans.naturality_apply α _ x).trans
      ((congrArg _ h).trans (NatTrans.naturality_apply α _ y).symm)
  · constructor
    intro U s p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    have := hi V hV
    exact ⟨V, homOfLE hVU, (ConcreteCategory.bijective_of_isIso (α.app (.op V))).2
      ((((Opens.map (pullback.snd X.hom Y.hom).base).op ⋙
        (pullback X.hom Y.hom).presheaf) ⋙ forget₂ CommRingCat RingCat).map (homOfLE hVU).op s),
      hpV⟩

/-- The inclusion of the quasi-coherent modules into all modules on a scheme preserves all
colimits in the scheme's universe: quasi-coherence is closed under them, so the inclusion
creates them. -/
private theorem preservesColimits_quasicoherentIota (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  refine ⟨fun {J} _ => ?_⟩
  have : (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape X
  have : HasColimitsOfShape J
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    Limits.hasColimitsOfShape_of_closedUnderColimits J _
  have : CreatesColimitsOfShape J (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    Limits.createsColimitsOfShapeFullSubcategoryInclusion J _
  exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _

/-- Restriction of scalars along a morphism of sheaves of rings on a scheme preserves all
colimits: it is the identity after forgetting the module structure. -/
private lemma restrictScalars_preservesColimits
    {S : Scheme.{u}} {R R' : Sheaf (Opens.grothendieckTopology S) RingCat.{u}}
    (α : R ⟶ R') :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) := by
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) := by
    show PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R')
    exact AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits R'
  constructor
  intro J _
  have : ReflectsColimitsOfShape J (SheafOfModules.toSheaf.{u} R) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (SheafOfModules.restrictScalars.{u} α) (SheafOfModules.toSheaf.{u} R)

/-- Direct image along an affine morphism, restricted to quasi-coherent modules, preserves all
colimits in the scheme's universe: it is an equivalence onto the quasi-coherent modules over
the direct image of the structure sheaf, followed by restriction of scalars. -/
private lemma affinePushforward_preservesColimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] :
    PreservesColimitsOfSize.{u, u}
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        Scheme.Modules.pushforward f) := by
  let P := SheafOfModules.isQuasicoherent
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf)
  let Q := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let G := SheafOfModules.restrictScalars f.toRingCatSheafHom
  let F := Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward f
  have : F.IsEquivalence :=
    Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward f
  have hG : PreservesColimitsOfSize.{u, u} G := restrictScalars_preservesColimits _
  constructor
  intro J _
  have : PreservesColimitsOfShape J G := hG.preservesColimitsOfShape
  have : Q.IsClosedUnderColimitsOfShape J :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape Y
  have hP : P = Q.inverseImage G := by
    funext M
    exact propext
      (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f M).symm
  have : P.IsClosedUnderColimitsOfShape J := by
    rw [hP]
    exact @ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage _ _ _ _ J _ Q G
      ‹Q.IsClosedUnderColimitsOfShape J› ‹PreservesColimitsOfShape J G›
  show PreservesColimitsOfShape J (F ⋙ P.ι ⋙ G)
  have : HasColimitsOfShape J (SheafOfModules.{u}
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing
      f.base X.ringCatSheaf)) := inferInstance
  have : CreatesColimitsOfShape J P.ι :=
    @createsColimitsOfShapeFullSubcategoryInclusion J _ _ _ P
      ‹P.IsClosedUnderColimitsOfShape J› inferInstance
  have : PreservesColimitsOfShape J P.ι := inferInstance
  have : PreservesColimitsOfShape J F := inferInstance
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ F (P.ι ⋙ G)
    ‹PreservesColimitsOfShape J F› (@comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ P.ι G
      ‹PreservesColimitsOfShape J P.ι› ‹PreservesColimitsOfShape J G›)

/-- Inverse image preserves quasi-coherence. -/
private lemma pullback_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom M
    ‹M.IsQuasicoherent›

/-- For `X` affine, the pullback--tensor--pushforward formula preserves all colimits in the
scheme's universe.  Inverse image and tensoring preserve all colimits, and the direct image
along the second projection does so on quasi-coherent modules because that projection is
affine and the formula takes quasi-coherent values. -/
private lemma integralTransformFormula_preservesColimits
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    PreservesColimitsOfSize.{u, u}
      (AlgebraicGeometry.integralTransformFormula R X Y K.obj) := by
  let P := pullback X.hom Y.hom
  let Q := SheafOfModules.isQuasicoherent P.ringCatSheaf
  let site := Opens.grothendieckTopology P.carrier
  let ring : Sheaf site CommRingCat := ⟨P.presheaf, P.IsSheaf⟩
  let ten : P.Modules ⥤ P.Modules :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
        (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K.obj))
  let T := (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
    Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙ ten
  have hT : ∀ M, Q (T.obj M) := by
    intro M
    have : K.obj.IsQuasicoherent := K.property
    have : M.obj.IsQuasicoherent := M.property
    have hM := pullback_isQuasicoherent (pullback.fst X.hom Y.hom) M.obj
    exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent
      P.toRingedSpace K.obj _ K.property hM
  let T' := ObjectProperty.lift Q T hT
  have hιX : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι :=
    preservesColimits_quasicoherentIota X.left
  have : PreservesColimitsOfSize.{u, u} ten :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits site ring K.obj
  have : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  have := affinePushforward_preservesColimits (pullback.snd X.hom Y.hom)
  have hT' : PreservesColimitsOfSize.{u, u} T' := by
    constructor
    intro J _
    have : (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).IsLeftAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction _).isLeftAdjoint
    have h1 : PreservesColimitsOfShape J
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι :=
      hιX.preservesColimitsOfShape
    have h2 : PreservesColimitsOfShape J
        (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)) := inferInstance
    have h3 : PreservesColimitsOfShape J ten :=
      ‹PreservesColimitsOfSize.{u, u} ten›.preservesColimitsOfShape
    have hTJ : PreservesColimitsOfShape J T :=
      @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h1
        (@comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h2 h3)
    exact @preservesColimitsOfShape_of_reflects_of_preserves _ _ _ _ J _ _ _
      T' Q.ι hTJ inferInstance
  show PreservesColimitsOfSize.{u, u}
    (T' ⋙ Q.ι ⋙ Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))
  infer_instance

/-- A natural transformation out of a colimit-preserving functor on modules over a commutative
ring is determined by its value on the rank-one free module: free modules are coproducts of
copies of it, and every module is a quotient of a free one. -/
private lemma moduleNatTrans_ext
    (A : Type u) [CommRing A] {B : Type*} [Category B]
    (F G : ModuleCat.{u} A ⥤ B) [PreservesColimitsOfSize.{u, u} F]
    [F.PreservesEpimorphisms] (α β : F ⟶ G)
    (h : α.app (ModuleCat.of A A) = β.app (ModuleCat.of A A)) : α = β := by
  have hfree (I : Type u) :
      α.app (ModuleCat.of A (I →₀ A)) = β.app (ModuleCat.of A (I →₀ A)) := by
    apply (isColimitOfPreserves F (ModuleCat.finsuppCoconeIsColimit A A I)).hom_ext
    intro i
    show F.map _ ≫ α.app _ = F.map _ ≫ β.app _
    rw [α.naturality, β.naturality]
    show α.app (ModuleCat.of A A) ≫ _ = β.app (ModuleCat.of A A) ≫ _
    rw [h]
  ext M
  let p : ModuleCat.of A (M →₀ A) ⟶ M :=
    ModuleCat.ofHom (Finsupp.linearCombination A (id : M → M))
  have : Epi p := (ModuleCat.epi_iff_surjective p).mpr (by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    simp [p])
  apply (cancel_epi (F.map p)).1
  rw [α.naturality, β.naturality, hfree]

/-- Inverse image, restricted to quasi-coherent modules. -/
private noncomputable def quasicoherentPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f)
    (fun M => @pullback_isQuasicoherent _ _ f M.obj M.property)

/-- An isomorphism of schemes induces an equivalence of their categories of quasi-coherent
modules, by inverse image. -/
private noncomputable def quasicoherentPullbackIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := by
  let F := quasicoherentPullback e.hom
  let G := quasicoherentPullback e.inv
  let η := Scheme.Modules.pullbackComp e.inv e.hom ≪≫
    Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y
  let ε := Scheme.Modules.pullbackComp e.hom e.inv ≪≫
    Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (η.app M.obj).symm)
      (by intro M N f; apply ObjectProperty.hom_ext; exact η.inv.naturality f.hom))
    (NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (ε.app M.obj))
      (by intro M N f; apply ObjectProperty.hom_ext; exact ε.hom.naturality f.hom))

/-- For `X` affine, modules over the ring of global functions are equivalent to quasi-coherent
modules on `X`. -/
private noncomputable def affineQuasicoherentEquivalence (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, ⊤) ≌ (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  tildeEquiv.trans (quasicoherentPullbackIso X.isoSpec)

/-- Two right exact, coproduct-preserving functors out of a category equivalent to a module
category are isomorphic as soon as they agree, equivariantly for the ring, on the image of the
rank-one free module. -/
private lemma functorIsoOfGeneratorIso
    {A : Type u} [Ring A] {C B : Type*} [Category C] [Category B]
    [Preadditive B] [HasCoproducts.{u} B] [HasCokernels B]
    (E : ModuleCat.{u} Aᵐᵒᵖ ≌ C) (O : C)
    (e : E.functor.obj (ModuleCat.of Aᵐᵒᵖ A) ≅ O)
    (F G : C ⥤ B) [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (hF : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (hG : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G)
    (t : F.obj O ≅ G.obj O)
    (ht : ∀ a : O ⟶ O, F.map a ≫ t.hom = t.hom ≫ G.map a) : Nonempty (F ≅ G) := by
  let F' : ModuleCat.RightExactCoproductPreservingFunctor A B :=
    ⟨E.functor ⋙ F, comp_preservesFiniteColimits _ _, fun I => by have := hF I; infer_instance⟩
  let G' : ModuleCat.RightExactCoproductPreservingFunctor A B :=
    ⟨E.functor ⋙ G, comp_preservesFiniteColimits _ _, fun I => by have := hG I; infer_instance⟩
  let T := ModuleCat.functorToRingActions A B
  have : T.IsEquivalence := ModuleCat.functorToRingActions_isEquivalence A B
  let t' : F'.obj.obj (ModuleCat.of Aᵐᵒᵖ A) ≅ G'.obj.obj (ModuleCat.of Aᵐᵒᵖ A) :=
    F.mapIso e ≪≫ t ≪≫ (G.mapIso e).symm
  let i : T.obj F' ≅ T.obj G' := ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ => t') (by
      intro i j a
      show F.map (E.functor.map (ModuleCat.regularModuleLeftMul A a)) ≫ t'.hom =
        t'.hom ≫ G.map (E.functor.map (ModuleCat.regularModuleLeftMul A a))
      have h := ht (e.inv ≫ E.functor.map (ModuleCat.regularModuleLeftMul A a) ≫ e.hom)
      dsimp [t']
      simpa only [Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, Functor.mapIso_inv, Iso.hom_inv_id_assoc, Iso.map_inv_hom_id_assoc,
        Iso.map_hom_inv_id_assoc, Iso.map_hom_inv_id, Category.comp_id] using
        congrArg (fun k => F.map e.hom ≫ k ≫ G.map e.inv) h))
  let j : E.functor ⋙ F ≅ E.functor ⋙ G :=
    (ObjectProperty.ι _).mapIso (T.preimageIso i)
  exact ⟨((Functor.whiskeringLeft _ _ B).obj E.functor).preimageIso j⟩

/-- Conjugating a commuting square of endomorphisms by two isomorphisms. -/
private lemma conjugate_commutes
    {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ A') (f : B ≅ B') (a : A ⟶ A) (b : B ⟶ B)
    (a' : A' ⟶ A') (b' : B' ⟶ B') (t : A ⟶ B)
    (ha : a ≫ e.hom = e.hom ≫ a') (hb : b ≫ f.hom = f.hom ≫ b')
    (ht : a ≫ t = t ≫ b) :
    a' ≫ (e.inv ≫ t ≫ f.hom) = (e.inv ≫ t ≫ f.hom) ≫ b' := by
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, ← ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ht, Category.assoc, hb]

/-- For `X` affine, the integral transform attached to a quasi-coherent kernel preserves all
colimits in the scheme's universe. -/
private lemma integralTransform_preservesColimits
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    PreservesColimitsOfSize.{u, u} (quasicoherentIntegralTransform R X Y K) := by
  let F := quasicoherentIntegralTransform R X Y K
  let G := (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
  have : PreservesColimitsOfSize.{u, u} (F ⋙ G) :=
    @preservesColimits_of_natIso _ _ _ _ _ _
      (AlgebraicGeometry.quasicoherentIntegralTransformData R X Y K).comparison.symm
      (integralTransformFormula_preservesColimits R X Y K)
  constructor
  intro J _
  exact preservesColimitsOfShape_of_reflects_of_preserves F G

/-- If `C` is the pushout of `f : S ⟶ A` and `g : S ⟶ B` in commutative rings, then two ring
homomorphisms `a : A →+* D` and `b : B →+* D` with pairwise commuting images that agree on `S`
extend to a ring homomorphism `C →+* D`. -/
private lemma exists_ringHomOfIsPushout
    {S A B C : CommRingCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ C} {j : B ⟶ C} (h : IsPushout f g i j)
    {D : Type u} [Ring D] (a : A →+* D) (b : B →+* D)
    (hab : ∀ x y, Commute (a x) (b y))
    (hf : a.comp f.hom = b.comp g.hom) :
    ∃ c : C →+* D, c.comp i.hom = a ∧ c.comp j.hom = b := by
  let T := Subring.closure (Set.range a ∪ Set.range b)
  have ht : ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b, x * y = y * x := by
    rintro x (⟨x, rfl⟩ | ⟨x, rfl⟩) y (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ((Commute.all x y).map a).eq
    · exact (hab x y).eq
    · exact (hab y x).symm.eq
    · exact ((Commute.all x y).map b).eq
  have : IsMulCommutative T := Subring.isMulCommutative_closure ht
  let _ : CommRing T := inferInstance
  let a' : A ⟶ CommRingCat.of T := CommRingCat.ofHom
    (a.codRestrict T (fun x => Subring.subset_closure (Or.inl ⟨x, rfl⟩)))
  let b' : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (b.codRestrict T (fun x => Subring.subset_closure (Or.inr ⟨x, rfl⟩)))
  have hf' : f ≫ a' = g ≫ b' := by
    ext x
    exact RingHom.congr_fun hf x
  refine ⟨T.subtype.comp (h.desc a' b' hf').hom, ?_, ?_⟩
  · ext x
    exact congrArg (fun k => T.subtype (k.hom x)) (h.inl_desc a' b' hf')
  · ext x
    exact congrArg (fun k => T.subtype (k.hom x)) (h.inr_desc a' b' hf')

/-- If `C` is the pushout of `f : S ⟶ A` and `g : S ⟶ B` in commutative rings, an additive map
between `C`-modules that is `A`-linear and `B`-linear is `C`-linear. -/
private lemma map_smul_of_isPushout
    {S A B C : CommRingCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {a : A ⟶ C} {b : B ⟶ C} (h : IsPushout f g a b)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module C M] [Module C N]
    (φ : M →+ N)
    (ha : ∀ r : A, ∀ x, φ (a.hom r • x) = a.hom r • φ x)
    (hb : ∀ r : B, ∀ x, φ (b.hom r • x) = b.hom r • φ x)
    (r : C) (x : M) : φ (r • x) = r • φ x := by
  let T : Subring C := {
    carrier := {r | ∀ x, φ (r • x) = r • φ x}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by
      intro r s hr hs x
      simp only [Set.mem_ofPred_eq] at hr hs
      simp [add_smul, hr, hs]
    neg_mem' := by
      intro r hr x
      simp only [Set.mem_ofPred_eq] at hr
      simp [neg_smul, hr]
    mul_mem' := by
      intro r s hr hs x
      simp only [Set.mem_ofPred_eq] at hr hs
      simp [mul_smul, hr, hs] }
  have hT : Subring.closure (Set.range a ∪ Set.range b) ≤ T := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact ha r
    · exact hb r
  rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout h] at hT
  exact hT (show r ∈ (⊤ : Subring C) from trivial) x

/-- A pair of natural actions of the presheaves of rings `A` and `B` on a presheaf of abelian
groups `M`, commuting with each other and agreeing on the common source `S`. -/
private structure CommutingPresheafActions
    {C : Type*} [Category C] {S A B : Cᵒᵖ ⥤ CommRingCat.{u}}
    (f : S ⟶ A) (g : S ⟶ B) (M : Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  /-- The action of `A` on `M`. -/
  left : ∀ U, A.obj U →+* AddMonoid.End (M.obj U)
  /-- The action of `B` on `M`. -/
  right : ∀ U, B.obj U →+* AddMonoid.End (M.obj U)
  /-- The two actions commute. -/
  commute : ∀ U a b, Commute (left U a) (right U b)
  /-- The two actions agree on sections pulled back from `S`. -/
  agree : ∀ U, (left U).comp (f.app U).hom = (right U).comp (g.app U).hom
  /-- The action of `A` is compatible with the restriction maps of `M`. -/
  left_naturality : ∀ {U V} (i : U ⟶ V) a x,
    M.map i (left U a x) = left V (A.map i a) (M.map i x)
  /-- The action of `B` is compatible with the restriction maps of `M`. -/
  right_naturality : ∀ {U V} (i : U ⟶ V) b x,
    M.map i (right U b x) = right V (B.map i b) (M.map i x)

/-- The action of the pushout presheaf of rings `A ⊔_S B` on `M` determined by a pair of
commuting actions of `A` and `B`, section by section. -/
private noncomputable def presheafPushoutAction
    {C : Type*} [Category C] {S A B : Cᵒᵖ ⥤ CommRingCat.{u}}
    {f : S ⟶ A} {g : S ⟶ B} {M : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (a : CommutingPresheafActions f g M) (U : Cᵒᵖ) :
    (pushout f g).obj U →+* AddMonoid.End (M.obj U) :=
  Classical.choose (exists_ringHomOfIsPushout
    ((IsPushout.of_hasPushout f g).map ((evaluation _ _).obj U))
    (a.left U) (a.right U) (a.commute U) (a.agree U))

/-- On sections coming from `A`, the pushout action is the given action of `A`. -/
private lemma presheafPushoutAction_left
    {C : Type*} [Category C] {S A B : Cᵒᵖ ⥤ CommRingCat.{u}}
    {f : S ⟶ A} {g : S ⟶ B} {M : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (a : CommutingPresheafActions f g M) (U : Cᵒᵖ) (r : A.obj U) :
    presheafPushoutAction a U ((pushout.inl f g).app U r) = a.left U r :=
  RingHom.congr_fun (Classical.choose_spec (exists_ringHomOfIsPushout
    ((IsPushout.of_hasPushout f g).map ((evaluation _ _).obj U))
    (a.left U) (a.right U) (a.commute U) (a.agree U))).1 r

/-- On sections coming from `B`, the pushout action is the given action of `B`. -/
private lemma presheafPushoutAction_right
    {C : Type*} [Category C] {S A B : Cᵒᵖ ⥤ CommRingCat.{u}}
    {f : S ⟶ A} {g : S ⟶ B} {M : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (a : CommutingPresheafActions f g M) (U : Cᵒᵖ) (r : B.obj U) :
    presheafPushoutAction a U ((pushout.inr f g).app U r) = a.right U r :=
  RingHom.congr_fun (Classical.choose_spec (exists_ringHomOfIsPushout
    ((IsPushout.of_hasPushout f g).map ((evaluation _ _).obj U))
    (a.left U) (a.right U) (a.commute U) (a.agree U))).2 r

/-- The presheaf of modules over the pushout presheaf of rings `A ⊔_S B` whose underlying
presheaf of abelian groups is `M`, with the action given by a pair of commuting actions. -/
private noncomputable def presheafPushoutModule
    {C : Type*} [Category C] {S A B : Cᵒᵖ ⥤ CommRingCat.{u}}
    {f : S ⟶ A} {g : S ⟶ B} {M : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (a : CommutingPresheafActions f g M) :
    PresheafOfModules.{u} (pushout f g ⋙ forget₂ CommRingCat RingCat) := by
  let : ∀ U : Cᵒᵖ, Module ((pushout f g ⋙ forget₂ CommRingCat RingCat).obj U) (M.obj U) :=
    fun U => Module.compHom _ (presheafPushoutAction a U)
  refine PresheafOfModules.ofPresheaf M ?_
  intro U V i r x
  let _mU : Module ((pushout f g).obj U) (M.obj U) :=
    Module.compHom _ (presheafPushoutAction a U)
  let _mV : Module ((pushout f g).obj V) (M.obj V) :=
    Module.compHom _ (presheafPushoutAction a V)
  let _mUV : Module ((pushout f g).obj U) (M.obj V) :=
    Module.compHom _ ((pushout f g).map i).hom
  apply map_smul_of_isPushout
    (C := (pushout f g).obj U)
    ((IsPushout.of_hasPushout f g).map ((evaluation _ _).obj U)) (M.map i).hom
  · intro r x
    change M.map i (presheafPushoutAction a U ((pushout.inl f g).app U r) x) =
      presheafPushoutAction a V ((pushout f g).map i ((pushout.inl f g).app U r)) (M.map i x)
    rw [presheafPushoutAction_left]
    have h := NatTrans.naturality_apply (pushout.inl f g) i r
    rw [← h, presheafPushoutAction_left]
    exact a.left_naturality i r x
  · intro r x
    change M.map i (presheafPushoutAction a U ((pushout.inr f g).app U r) x) =
      presheafPushoutAction a V ((pushout f g).map i ((pushout.inr f g).app U r)) (M.map i x)
    rw [presheafPushoutAction_right]
    have h := NatTrans.naturality_apply (pushout.inr f g) i r
    rw [← h, presheafPushoutAction_right]
    exact a.right_naturality i r x

/-- The sheaf of modules over a sheaf of rings `T` that locally identifies the pushout
`A ⊔_S B` of presheaves of rings, built from a sheaf `M` of abelian groups carrying a pair of
commuting actions of `A` and `B`. -/
private noncomputable def sheafPushoutModule
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {S A B : Cᵒᵖ ⥤ CommRingCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {T : Sheaf J RingCat.{u}} (α : (pushout f g ⋙ forget₂ CommRingCat RingCat) ⟶ T.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    {M : Sheaf J AddCommGrpCat.{u}} (a : CommutingPresheafActions f g M.obj) :
    SheafOfModules.{u} T := by
  let N := presheafPushoutModule a
  let φ : N.presheaf ⟶ M.obj := 𝟙 _
  have : IsIso φ := inferInstanceAs (IsIso (𝟙 M.obj))
  exact PresheafOfModules.sheafify α φ

/-- Sections of `A` act on `sheafPushoutModule α a` through the given action of `A`. -/
private lemma sheafPushoutModule_smul_left
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {S A B : Cᵒᵖ ⥤ CommRingCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {T : Sheaf J RingCat.{u}} (α : (pushout f g ⋙ forget₂ CommRingCat RingCat) ⟶ T.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    {M : Sheaf J AddCommGrpCat.{u}} (a : CommutingPresheafActions f g M.obj)
    (U : Cᵒᵖ) (r : A.obj U) (x : M.obj.obj U) :
    (α.app U ((pushout.inl f g).app U r) •
      (show (sheafPushoutModule α a).val.obj U from x) : (sheafPushoutModule α a).val.obj U) =
      a.left U r x := by
  let N := presheafPushoutModule a
  let φ : N.presheaf ⟶ M.obj := 𝟙 _
  have : IsIso φ := inferInstanceAs (IsIso (𝟙 M.obj))
  have h := ((PresheafOfModules.toSheafify α φ).app U).hom.map_smul
    ((pushout.inl f g).app U r) x
  change presheafPushoutAction a U ((pushout.inl f g).app U r) x = _ at h
  rw [presheafPushoutAction_left] at h
  exact h.symm

/-- Sections of `B` act on `sheafPushoutModule α a` through the given action of `B`. -/
private lemma sheafPushoutModule_smul_right
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {S A B : Cᵒᵖ ⥤ CommRingCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {T : Sheaf J RingCat.{u}} (α : (pushout f g ⋙ forget₂ CommRingCat RingCat) ⟶ T.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    {M : Sheaf J AddCommGrpCat.{u}} (a : CommutingPresheafActions f g M.obj)
    (U : Cᵒᵖ) (r : B.obj U) (x : M.obj.obj U) :
    (α.app U ((pushout.inr f g).app U r) •
      (show (sheafPushoutModule α a).val.obj U from x) : (sheafPushoutModule α a).val.obj U) =
      a.right U r x := by
  let N := presheafPushoutModule a
  let φ : N.presheaf ⟶ M.obj := 𝟙 _
  have : IsIso φ := inferInstanceAs (IsIso (𝟙 M.obj))
  have h := ((PresheafOfModules.toSheafify α φ).app U).hom.map_smul
    ((pushout.inr f g).app U r) x
  change presheafPushoutAction a U ((pushout.inr f g).app U r) x = _ at h
  rw [presheafPushoutAction_right] at h
  exact h.symm

/-- For `X` affine over `R` and `U` an affine open of `Y`, an `𝒪_Y`-linear map between two
sheaves of modules over `(pr₂)_* 𝒪_{X ×_R Y}` is linear for all of `Γ(X ×_R Y, pr₂ ⁻¹ᵁ U)` as
soon as it is linear for the sections of `X`. -/
private lemma affine_pushforward_map_smul
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (M N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf))
    (φ : (SheafOfModules.restrictScalars (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj M ⟶
      (SheafOfModules.restrictScalars (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (ha : ∀ a : Γ(X.left, ⊤), ∀ x : M.val.obj (.op U),
      φ.val.app (.op U)
          ((show (pushforwardRing (pullback.snd X.hom Y.hom).base
              (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U) from
            (pullback.fst X.hom Y.hom).appLE ⊤ ((pullback.snd X.hom Y.hom) ⁻¹ᵁ U)
              (le_top.trans (le_of_eq (pullback.fst X.hom Y.hom).preimage_top.symm)) a) • x) =
        (show (pushforwardRing (pullback.snd X.hom Y.hom).base
            (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U) from
          (pullback.fst X.hom Y.hom).appLE ⊤ ((pullback.snd X.hom Y.hom) ⁻¹ᵁ U)
            (le_top.trans (le_of_eq (pullback.fst X.hom Y.hom).preimage_top.symm)) a) •
          (show N.val.obj (.op U) from φ.val.app (.op U) x))
    (r : Γ(pullback X.hom Y.hom, (pullback.snd X.hom Y.hom) ⁻¹ᵁ U))
    (x : M.val.obj (.op U)) :
    φ.val.app (.op U)
        ((show (pushforwardRing (pullback.snd X.hom Y.hom).base
          (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U) from r) • x) =
      (show (pushforwardRing (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U) from r) •
        (show N.val.obj (.op U) from φ.val.app (.op U) x) := by
  let _mM : Module ↑Γ(pullback X.hom Y.hom, (pullback.snd X.hom Y.hom) ⁻¹ᵁ U)
      ↑(M.val.obj (.op U)) :=
    inferInstanceAs (Module ↑((pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U)) ↑(M.val.obj (.op U)))
  let _mN : Module ↑Γ(pullback X.hom Y.hom, (pullback.snd X.hom Y.hom) ⁻¹ᵁ U)
      ↑(N.val.obj (.op U)) :=
    inferInstanceAs (Module ↑((pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj.obj (.op U)) ↑(N.val.obj (.op U)))
  let H := IsPullback.of_hasPullback X.hom Y.hom
  have hi := isIso_pushoutSection_of_isAffineOpen H
    (US := ⊤) (UT := U) (UX := ⊤)
    (le_top.trans (le_of_eq Y.hom.preimage_top.symm))
    (le_top.trans (le_of_eq X.hom.preimage_top.symm))
    (UY := (pullback.snd X.hom Y.hom) ⁻¹ᵁ U) (by simp)
    (isAffineOpen_top (Spec (.of R))) hU (isAffineOpen_top X.left)
  let hp := (isIso_pushoutSection_iff H
    (US := ⊤) (UT := U) (UX := ⊤)
    (le_top.trans (le_of_eq Y.hom.preimage_top.symm))
    (le_top.trans (le_of_eq X.hom.preimage_top.symm))
    (UY := (pullback.snd X.hom Y.hom) ⁻¹ᵁ U) (by simp)).mp hi
  exact map_smul_of_isPushout (M := M.val.obj (.op U)) (N := N.val.obj (.op U)) hp
    (φ.val.app (.op U)).hom.toAddMonoidHom ha
    (fun b x => by
      rw [Scheme.Hom.appLE_eq_app]
      exact (φ.val.app (.op U)).hom.map_smul b x) r x

/-- A morphism of sheaves of modules over `S` between the scalar restrictions of two sheaves of
modules over `T` is `T`-linear on every open as soon as it is `T`-linear on affine opens. -/
private lemma map_smul_of_affineOpen
    {Y : Scheme.{u}} {S T : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    (a : S ⟶ T) (M N : SheafOfModules.{u} T)
    (φ : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (h : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (r : T.obj.obj (.op U))
      (x : M.val.obj (.op U)),
      φ.val.app (.op U) (r • x) = r • (show N.val.obj (.op U) from φ.val.app (.op U) x))
    (U : Y.Opens) (r : T.obj.obj (.op U)) (x : M.val.obj (.op U)) :
    φ.val.app (.op U) (r • x) = r • (show N.val.obj (.op U) from φ.val.app (.op U) x) := by
  let I := {V : Y.Opens // IsAffineOpen V ∧ V ≤ U}
  let V : I → Y.Opens := fun i => i.val
  have hc : U ≤ iSup V := by
    intro y hy
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hyW⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (X := Y.toTopCat) ((SheafOfModules.toSheaf T).obj N) V U
    (fun i => homOfLE i.property.2) hc
  intro i
  show N.val.map (homOfLE i.property.2).op (φ.val.app (.op U) (r • x)) =
    N.val.map (homOfLE i.property.2).op
      (r • (show N.val.obj (.op U) from φ.val.app (.op U) x))
  have hn (z : M.val.obj (.op U)) :=
    PresheafOfModules.naturality_apply φ.val (homOfLE i.property.2).op z
  change ∀ z : M.val.obj (.op U), φ.val.app (.op i.val) (M.val.map (homOfLE i.property.2).op z) =
      N.val.map (homOfLE i.property.2).op (φ.val.app (.op U) z) at hn
  rw [← hn, M.val.map_smul, N.val.map_smul, ← hn]
  exact h i.val i.property.1 _ _

/-- A morphism between the scalar restrictions along `a : S ⟶ T` of two sheaves of modules over
`T`, which is `T`-linear on affine opens, as a morphism of sheaves of modules over `T`. -/
private noncomputable def liftRestrictScalarsHom
    {Y : Scheme.{u}} {S T : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    (a : S ⟶ T) (M N : SheafOfModules.{u} T)
    (φ : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (h : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (r : T.obj.obj (.op U))
      (x : M.val.obj (.op U)),
      φ.val.app (.op U) (r • x) = r • (show N.val.obj (.op U) from φ.val.app (.op U) x)) :
    M ⟶ N where
  val.app U := ModuleCat.ofHom {
    __ := (φ.val.app U).hom.toAddMonoidHom
    map_smul' r x := map_smul_of_affineOpen a M N φ h U.unop r x }
  val.naturality f := by
    ext x
    exact PresheafOfModules.naturality_apply φ.val f x

/-- Restricting scalars undoes the lift of a scalar-restricted morphism. -/
private lemma restrictScalars_map_liftRestrictScalarsHom
    {Y : Scheme.{u}} {S T : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    (a : S ⟶ T) (M N : SheafOfModules.{u} T)
    (φ : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars a).obj N)
    (h : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (r : T.obj.obj (.op U))
      (x : M.val.obj (.op U)),
      φ.val.app (.op U) (r • x) = r • (show N.val.obj (.op U) from φ.val.app (.op U) x)) :
    (SheafOfModules.restrictScalars a).map (liftRestrictScalarsHom a M N φ h) = φ := rfl

/-- The inclusion of the quasi-coherent modules into all modules on a scheme is right exact. -/
private alias preservesFiniteColimits_quasicoherentIota :=
  AlgebraicGeometry.preservesFiniteColimits_quasicoherentι

/-- Tensoring on the right by a sheaf of modules isomorphic to the structure sheaf is the
identity functor, by the right unit constraint of the sheaf tensor product. -/
noncomputable def tensorRightUnitIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (e : P ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Functor.curry.obj
        (Stacks.SheafOfModules.Invertible.tensorProductBifunctor O hO)).flip.obj P ≅ 𝟭 _ := by
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
    PresheafOfModules.monoidalCategory (R := O)
  let U := SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
  let L := Stacks.SheafOfModules.TensorSheafification.sheafify O hO
  let t := (MonoidalCategory.tensoringRight _).mapIso (U.mapIso e) ≪≫
    MonoidalCategory.rightUnitorNatIso _
  let hc : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft U t) L ≪≫ (@asIso _ _ _ _ _ hc)

/-- The component of `tensorRightUnitIso` at a sheaf of modules `K` is the sheaf tensor
product of the identity of `K` with `e`, followed by the right unit constraint. -/
private lemma tensorRightUnitIso_hom_app
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (e : P ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (K : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorRightUnitIso O hO P e).hom.app K =
      (Stacks.SheafOfModules.Invertible.tensorProductIso O hO (Iso.refl K) e ≪≫
        Stacks.SheafOfModules.Invertible.tensorProductRightUnitor O hO K).hom := by
  let _i : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
    PresheafOfModules.monoidalCategory (R := O)
  have hL : (tensorRightUnitIso O hO P e).hom.app K =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          ((K.val ◁ (SheafOfModules.forget
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom) ≫
            (ρ_ K.val).hom) ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit.app K := rfl
  have hR : (Stacks.SheafOfModules.Invertible.tensorProductIso O hO (Iso.refl K) e ≪≫
        Stacks.SheafOfModules.Invertible.tensorProductRightUnitor O hO K).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (K.val ◁ (SheafOfModules.forget
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ K.val).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit.app K) := rfl
  have hm : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        ((K.val ◁ (SheafOfModules.forget
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom) ≫
          (ρ_ K.val).hom) =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (K.val ◁ (SheafOfModules.forget
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom) ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ K.val).hom :=
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map_comp _ _
  rw [hL, hR, hm]
  exact Category.assoc _ _ _

/-- Multiplication by a global section `a` of the structure sheaf, as an endomorphism of a
sheaf of modules: on sections over `U` it is scalar multiplication by the restriction of `a`. -/
noncomputable def sectionScalar (X : Scheme.{u}) (a : Γ(X, ⊤))
    (M : X.Modules) : M ⟶ M where
  val.app U := by
    let : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    exact ModuleCat.ofHom
      ((show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a) •
        LinearMap.id (R := X.ringCatSheaf.obj.obj U) (M := M.val.obj U))
  val.naturality {U V} f := by
    ext x
    change (show X.ringCatSheaf.obj.obj V from X.presheaf.map V.unop.leTop.op a) •
        (show M.val.obj V from M.val.map f x) =
      M.val.map f
        ((show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a) • x)
    rw [M.val.map_smul]
    congr 1
    exact (congrArg (fun k => k a) (X.presheaf.map_comp U.unop.leTop.op f))

/-- Multiplication by a global section of the structure sheaf is natural in the module. -/
lemma sectionScalar_naturality (X : Scheme.{u}) (a : Γ(X, ⊤))
    {M N : X.Modules} (f : M ⟶ N) :
    sectionScalar X a M ≫ f = f ≫ sectionScalar X a N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (f.val.app U).hom.map_smul _ x

/-- The action of the global sections of the structure sheaf on a sheaf of modules, as a ring
homomorphism to the endomorphism ring of the module. -/
@[ega "0 5.4.3" "partial"]
noncomputable def sectionScalarRingHom (X : Scheme.{u}) (M : X.Modules) :
    Γ(X, ⊤) →+* End M where
  toFun a := sectionScalar X a M
  map_one' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op 1) • x = x
    simp only [map_one]
    exact @one_smul (X.ringCatSheaf.obj.obj U) (M.val.obj U) _ _ x
  map_mul' a b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op (a * b)) • x =
      (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a) •
        ((show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op b) • x)
    simp only [map_mul]
    exact mul_smul _ _ x
  map_zero' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op 0) • x = 0
    simp only [map_zero]
    exact zero_smul _ x
  map_add' a b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op (a + b)) • x =
      (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a) • x +
        (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op b) • x
    simp only [map_add]
    exact @add_smul (X.ringCatSheaf.obj.obj U) (M.val.obj U) _ _ _ _ _ x

/-- Every endomorphism of the structure sheaf as a module over itself is multiplication by a
global section, namely the image of `1` under the endomorphism. -/
lemma sectionScalar_unit_surjective (X : Scheme.{u})
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ∃ a, sectionScalar X a _ = f := by
  refine ⟨f.val.app (.op ⊤) (1 : Γ(X, ⊤)), ?_⟩
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change X.presheaf.obj U at x
  have h := PresheafOfModules.naturality_apply f.val U.unop.leTop.op (1 : Γ(X, ⊤))
  change f.val.app U (X.presheaf.map U.unop.leTop.op 1) =
    X.presheaf.map U.unop.leTop.op (f.val.app (.op ⊤) (1 : Γ(X, ⊤))) at h
  rw [map_one] at h
  show X.presheaf.map U.unop.leTop.op (f.val.app (.op ⊤) (1 : Γ(X, ⊤))) * x = f.val.app U x
  exact (congrArg (fun r => r * x) h.symm).trans
    ((mul_comm _ _).trans
      (((f.val.app U).hom.map_smul x (1 : X.presheaf.obj U)).symm.trans
        (congrArg (f.val.app U).hom (mul_one x))))

/-- Evaluation of endomorphisms of a sheaf of modules on sections over a fixed open set, as a
ring homomorphism to the additive endomorphisms of the sections. -/
noncomputable def sheafEndEvaluation {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opensᵒᵖ) : End M →+* AddMonoid.End (M.val.obj U) where
  toFun f := (f.val.app U).hom.toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- For a scheme over `R`, multiplication by the image of `r : R` in the global sections of the
structure sheaf is the action of `r` coming from the `R`-linear structure on module sheaves. -/
lemma sectionScalar_base (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (r : R) (M : X.left.Modules) :
    letI : Linear R X.left.Modules := AlgebraicGeometry.modulesLinear R X
    sectionScalar X.left (X.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) M = r • 𝟙 M := by
  dsimp only
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show (show X.left.ringCatSheaf.obj.obj U from X.left.presheaf.map U.unop.leTop.op
      (X.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) • x =
    ((AlgebraicGeometry.baseScalar R X r).app M).val.app U x
  rfl

/-- The action of the global sections of the structure sheaf on a quasi-coherent module sheaf,
as a ring homomorphism to its endomorphism ring. -/
noncomputable def quasicoherentSectionScalarRingHom (X : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Γ(X, ⊤) →+* End M where
  toFun a := ObjectProperty.homMk (sectionScalar X a M.obj)
  map_one' := ObjectProperty.hom_ext _ (sectionScalarRingHom X M.obj).map_one
  map_mul' a b := ObjectProperty.hom_ext _ ((sectionScalarRingHom X M.obj).map_mul a b)
  map_zero' := ObjectProperty.hom_ext _ (sectionScalarRingHom X M.obj).map_zero
  map_add' a b := ObjectProperty.hom_ext _ ((sectionScalarRingHom X M.obj).map_add a b)

/-- On quasi-coherent module sheaves over a scheme over `R`, multiplication by the image of
`r : R` in the global sections is the action of `r` from the `R`-linear structure. -/
lemma quasicoherentSectionScalar_base (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (r : R)
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) :=
      AlgebraicGeometry.modulesLinear R X
    quasicoherentSectionScalarRingHom X.left M
      (X.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) = r • 𝟙 M := by
  apply ObjectProperty.hom_ext
  exact sectionScalar_base R X r M.obj

/-- An additive functor induces a ring homomorphism on endomorphism rings. -/
noncomputable def additiveMapEnd
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (M : C) : End M →+* End (F.obj M) :=
  { F.mapEnd M with
    map_zero' := F.map_zero _ _
    map_add' := fun _ _ => F.map_add }

/-- Multiplication by a global section commutes with the identification of the pullback of the
structure sheaf, for the pulled-back section. -/
lemma pullbackUnitIso_sectionScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (sectionScalar Y a (SheafOfModules.unit Y.ringCatSheaf)) ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso f).hom ≫
        sectionScalar X (f.appTop a) (SheafOfModules.unit X.ringCatSheaf) := by
  have key : sectionScalar Y a (SheafOfModules.unit Y.ringCatSheaf) ≫
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward f).map
        (sectionScalar X (f.appTop a) (SheafOfModules.unit X.ringCatSheaf)) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ↑(Y.presheaf.obj U) at x
    show f.app U.unop (Y.presheaf.map U.unop.leTop.op a * x) =
      X.presheaf.map (f ⁻¹ᵁ U.unop).leTop.op (f.appTop a) * f.app U.unop x
    rw [map_mul]
    congr 1
    exact congrArg (fun k => k a) (f.naturality U.unop.leTop.op)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  exact (adj.homEquiv_naturality_left_symm
      (sectionScalar Y a (SheafOfModules.unit Y.ringCatSheaf))
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).symm.trans
    ((congrArg (adj.homEquiv _ _).symm key).trans
      (adj.homEquiv_naturality_right_symm _ _))

/-- The integral transform of a kernel, evaluated at the structure sheaf, is the pushforward of
the kernel along the second projection. -/
noncomputable def integralTransformUnitIso (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (pullback X.hom Y.hom).Modules) :
    (AlgebraicGeometry.integralTransformFormula R X Y K).obj
        ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≅
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K := by
  let P := pullback X.hom Y.hom
  let p₁ := pullback.fst X.hom Y.hom
  let p₂ := pullback.snd X.hom Y.hom
  let e₁ := Scheme.Modules.pullbackUnitIso p₁
  let e₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
        (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K))).obj
      ((Scheme.Modules.pullback p₁).obj (SheafOfModules.unit X.left.ringCatSheaf)) ≅ K := by
    change (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
        (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K)).obj
      (((Scheme.Modules.pullback p₁).obj (SheafOfModules.unit X.left.ringCatSheaf)))) ≅ K
    exact (Stacks.SheafOfModules.Invertible.tensorProductIso P.presheaf P.ringCatSheaf.2
        (Iso.refl K) e₁) ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductRightUnitor P.presheaf P.ringCatSheaf.2 K
  change (Scheme.Modules.pushforward p₂).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
          (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K))).obj
        ((Scheme.Modules.pullback p₁).obj (SheafOfModules.unit X.left.ringCatSheaf))) ≅ _
  exact (Scheme.Modules.pushforward p₂).mapIso e₂

/-- Two commuting squares of endomorphisms side by side compose to a commuting square. -/
private lemma comp_commutes_of_commutes
    {C : Type*} [Category C] {A B D : C} {a : A ⟶ A} {b : B ⟶ B} {c : D ⟶ D}
    {u : A ⟶ B} {v : B ⟶ D} (h : a ≫ u = u ≫ b) (h' : b ≫ v = v ≫ c) :
    a ≫ u ≫ v = (u ≫ v) ≫ c := by
  rw [← Category.assoc, h, Category.assoc, h', Category.assoc]

/-- Multiplication by a global section commutes with the right unit constraint of the sheaf
tensor product. -/
lemma tensorRightUnitor_sectionScalar (X : Scheme.{u}) (a : Γ(X, ⊤))
    (M : X.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
        (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (M))).map
        (sectionScalar X a (SheafOfModules.unit X.ringCatSheaf)) ≫
        (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
          X.ringCatSheaf.2 M).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
          X.ringCatSheaf.2 M).hom ≫ sectionScalar X a M := by
  let _ : MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let L := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf X.ringCatSheaf.2
  let ε := (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
    X.ringCatSheaf.2).counit
  have ht : (M.val ◁ (sectionScalar X a (SheafOfModules.unit X.ringCatSheaf)).val) ≫
        (ρ_ M.val).hom = (ρ_ M.val).hom ≫ (sectionScalar X a M).val := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    refine TensorProduct.ext' (R := X.presheaf.obj U)
      (M := M.val.obj U) (N := X.presheaf.obj U)
      (R₂ := X.presheaf.obj U) (σ₁₂ := RingHom.id _) (P₂ := M.val.obj U) ?_
    intro m r
    show (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a * r) • m =
      (show X.ringCatSheaf.obj.obj U from X.presheaf.map U.unop.leTop.op a) • (r • m)
    exact mul_smul _ _ _
  have hn := ε.naturality (sectionScalar X a M)
  change L.map (sectionScalar X a M).val ≫ ε.app M = ε.app M ≫ sectionScalar X a M at hn
  show L.map (M.val ◁ (sectionScalar X a (SheafOfModules.unit X.ringCatSheaf)).val) ≫
    (L.map (ρ_ M.val).hom ≫ ε.app M) =
      (L.map (ρ_ M.val).hom ≫ ε.app M) ≫ sectionScalar X a M
  exact comp_commutes_of_commutes ((L.map_comp _ _).symm.trans
    ((congrArg L.map ht).trans (L.map_comp _ _))) hn

/-- Multiplication by a global section of the structure sheaf of `X` corresponds, under the
identification of the integral transform at the structure sheaf with the pushforward of the
kernel, to multiplication by its pullback to `X ×_R Y`. -/
lemma integralTransformUnitIso_sectionScalar
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (pullback X.hom Y.hom).Modules) (a : Γ(X.left, ⊤)) :
    (AlgebraicGeometry.integralTransformFormula R X Y K).map
        (ObjectProperty.homMk
          (sectionScalar X.left a (SheafOfModules.unit X.left.ringCatSheaf))) ≫
        (integralTransformUnitIso R X Y K).hom =
      (integralTransformUnitIso R X Y K).hom ≫
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          (sectionScalar (pullback X.hom Y.hom) ((pullback.fst X.hom Y.hom).appTop a) K) := by
  let P := pullback X.hom Y.hom
  let p := pullback.fst X.hom Y.hom
  let q := pullback.snd X.hom Y.hom
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
      (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K))
  let rho := (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor P.presheaf
    P.ringCatSheaf.2 K).hom
  have ht := congrArg T.map (pullbackUnitIso_sectionScalar p a)
  have key : T.map ((Scheme.Modules.pullback p).map
        (sectionScalar X.left a (SheafOfModules.unit X.left.ringCatSheaf))) ≫
      (T.map (Scheme.Modules.pullbackUnitIso p).hom ≫ rho) =
    (T.map (Scheme.Modules.pullbackUnitIso p).hom ≫ rho) ≫ sectionScalar P (p.appTop a) K := by
    exact comp_commutes_of_commutes ((T.map_comp _ _).symm.trans (ht.trans (T.map_comp _ _)))
      (tensorRightUnitor_sectionScalar P (p.appTop a) K)
  exact (((Scheme.Modules.pushforward q).map_comp _ _).symm.trans
    (congrArg (Scheme.Modules.pushforward q).map key)).trans
      ((Scheme.Modules.pushforward q).map_comp _ _)

/-- The pullback to `X ×_R Y` of a global function on `X`, read as a section over an open of
`Y` of the direct image of the structure sheaf along the second projection. -/
private noncomputable abbrev sectionToProduct (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) (U : Y.left.Opensᵒᵖ) (a : Γ(X.left, ⊤)) :
    (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj.obj U :=
  (constantToProduct R X Y).app U a

/-- An action of the ring of global functions of the affine `X` on a quasi-coherent module on
`Y` which restricts on `R` to the canonical scalar action comes from a module over the direct
image of the structure sheaf of `X ×_R Y` along the second projection: over an affine open of
`Y` the sections of that sheaf of rings are the pushout of the two rings that act. -/
private lemma exists_pushforwardModule_of_sectionAction
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (M : Y.left.Modules) (ρ : Γ(X.left, ⊤) →+* End M)
    (hρ : ∀ r : Γ(Spec (.of R), ⊤),
      ρ (X.hom.appTop r) = sectionScalar Y.left (Y.hom.appTop r) M) :
    ∃ N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf),
      ∃ e : (SheafOfModules.restrictScalars
        (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅ M,
      ∀ (U : Y.left.Opensᵒᵖ) (a : Γ(X.left, ⊤)) (x : N.val.obj U),
        e.hom.val.app U (sectionToProduct R X Y U a • x) =
          (ρ a).val.app U (e.hom.val.app U x) := by
  let T := pushforwardRing (pullback.snd X.hom Y.hom).base
    (pullback X.hom Y.hom).ringCatSheaf
  let α := Functor.whiskerRight (productStructurePresheafMap R X Y)
    (forget₂ CommRingCat RingCat)
  have hα := productStructurePresheafMap_locallyBijective R X Y
  let act : CommutingPresheafActions
      ((Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop) (constantToStructure Y.hom)
      ((SheafOfModules.toSheaf _).obj M).obj := {
    left U := (sheafEndEvaluation M U).comp ρ
    right U := Module.toAddMonoidEnd (Y.left.presheaf.obj U) (M.val.obj U)
    commute U a b := by
      ext x
      exact ((ρ a).val.app U).hom.map_smul b x
    agree U := by
      ext r x
      show (ρ (X.hom.appTop r)).val.app U x =
        (show Y.left.ringCatSheaf.obj.obj U from
          (Y.hom.appLE ⊤ U.unop
            (le_top.trans (le_of_eq Y.hom.preimage_top.symm))) r) •
          (show M.val.obj U from x)
      rw [hρ]
      rfl
    left_naturality i a x := (PresheafOfModules.naturality_apply (ρ a).val i x).symm
    right_naturality i b x := M.val.map_smul i b x }
  let N := @sheafPushoutModule _ _ _ _ _ _ _ _ T α hα.1 hα.2 _ act
  have hr (U : Y.left.Opensᵒᵖ) (r : Y.left.presheaf.obj U) (x : M.val.obj U) :
      ((show T.obj.obj U from (pullback.snd X.hom Y.hom).c.app U r) •
          (show N.val.obj U from x) : N.val.obj U) =
        (show N.val.obj U from r • x) := by
    have h := @sheafPushoutModule_smul_right _ _ _ _ _ _ _ _ T α hα.1 hα.2 _ act U r x
    have he := congrArg (fun t => t.app U r)
      (pushout.inr_desc (constantToProduct R X Y) (pullback.snd X.hom Y.hom).c
        (productStructureSquare R X Y))
    change (show T.obj.obj U from α.app U
        ((pushout.inr ((Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop)
          (constantToStructure Y.hom)).app U r)) = _ at he
    exact (congrArg (fun z : T.obj.obj U => (z • (show N.val.obj U from x) :
      N.val.obj U)) he.symm).trans h
  let e : (SheafOfModules.restrictScalars
      (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅ M := {
    hom.val := PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun U r x => hr U r x)
    inv.val := PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun U r x => (hr U r x).symm)
    hom_inv_id := by ext U x; rfl
    inv_hom_id := by ext U x; rfl }
  refine ⟨N, e, ?_⟩
  intro U b x
  have h := @sheafPushoutModule_smul_left _ _ _ _ _ _ _ _ T α hα.1 hα.2 _ act U b x
  have he := congrArg (fun t => t.app U b)
    (pushout.inl_desc (constantToProduct R X Y) (pullback.snd X.hom Y.hom).c
      (productStructureSquare R X Y))
  change (show T.obj.obj U from α.app U
      ((pushout.inl ((Functor.const Y.left.Opensᵒᵖ).map X.hom.appTop)
        (constantToStructure Y.hom)).app U b)) = _ at he
  exact (congrArg (fun z : T.obj.obj U => (z • (show N.val.obj U from x) :
    N.val.obj U)) he.symm).trans h

/-- Evaluating the kernel-functorial formula on the structure sheaf gives the direct image
along the second projection. -/
private noncomputable def formulaFunctorUnitIso
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) :
    formulaFunctor R X Y ⋙
        (evaluation _ _).obj
          ⟨SheafOfModules.unit X.left.ringCatSheaf,
            Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≅
      Scheme.Modules.pushforward (pullback.snd X.hom Y.hom) := by
  let e := Functor.isoWhiskerRight
    (tensorRightUnitIso (pullback X.hom Y.hom).presheaf
      (pullback X.hom Y.hom).ringCatSheaf.2 _
      (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom)))
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
      Functor.leftUnitor _
  refine NatIso.ofComponents (fun K => e.app K) ?_
  intro K L f
  have h := e.hom.naturality f
  simp only [formulaFunctor, Functor.comp_map, evaluation_obj_map] at h ⊢
  exact h

/-- The component of `formulaFunctorUnitIso` at a kernel is `integralTransformUnitIso`. -/
private lemma formulaFunctorUnitIso_hom_app
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (pullback X.hom Y.hom).Modules) :
    (formulaFunctorUnitIso R X Y).hom.app K =
      (integralTransformUnitIso R X Y K).hom := by
  have h1 : (formulaFunctorUnitIso R X Y).hom.app K =
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          ((tensorRightUnitIso (pullback X.hom Y.hom).presheaf
            (pullback X.hom Y.hom).ringCatSheaf.2 _
            (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom))).hom.app K) ≫ 𝟙 _ := rfl
  have h2 : (integralTransformUnitIso R X Y K).hom =
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
        (Stacks.SheafOfModules.Invertible.tensorProductIso (pullback X.hom Y.hom).presheaf
            (pullback X.hom Y.hom).ringCatSheaf.2 (Iso.refl K)
            (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom)) ≪≫
          Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
            (pullback X.hom Y.hom).presheaf (pullback X.hom Y.hom).ringCatSheaf.2 K).hom := rfl
  have h3 := tensorRightUnitIso_hom_app (pullback X.hom Y.hom).presheaf
    (pullback X.hom Y.hom).ringCatSheaf.2
    ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj (Scheme.unitModule X.left))
    (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom)) K
  rw [h1, h3, h2]
  exact Category.comp_id _

/-- For `X` affine, the kernel-functorial formula is faithful in the kernel: a natural
transformation is determined by its value on the structure sheaf, where the formula is direct
image along the affine second projection. -/
private lemma formulaFunctor_faithful
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      formulaFunctor R X Y).Faithful := by
  have : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  refine ⟨fun {K L} f g h => ?_⟩
  apply pushforward_map_injective (pullback.snd X.hom Y.hom)
  let e := formulaFunctorUnitIso R X Y
  apply (cancel_mono (e.app L.obj).inv).1
  show _ ≫ e.inv.app L.obj = _ ≫ e.inv.app L.obj
  rw [e.inv.naturality f.hom, e.inv.naturality g.hom]
  congr 1
  exact congrArg (fun t => t.app
    ⟨SheafOfModules.unit X.left.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩) h

/-- The structure sheaf corresponds to the rank-one free module under the equivalence between
modules over the ring of global functions and quasi-coherent modules on an affine scheme. -/
private noncomputable def affineQuasicoherentEquivalenceUnitIso
    (X : Scheme.{u}) [IsAffine X] :
    (affineQuasicoherentEquivalence X).functor.obj (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)) ≅
      ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩ :=
  ObjectProperty.isoMk _ (Scheme.Modules.pullbackUnitIso X.isoSpec.hom)

/-- Two right exact, coproduct-preserving functors out of the quasi-coherent modules on an
affine scheme are isomorphic as soon as they agree on the structure sheaf, equivariantly for
its endomorphisms. -/
lemma affineFunctorIsoOfUnitIso (X : Scheme.{u}) [IsAffine X]
    {B : Type*} [Category B] [Preadditive B] [HasCoproducts.{u} B] [HasCokernels B]
    (F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ B)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (hF : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (hG : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G)
    (t : F.obj ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩ ≅
      G.obj ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩)
    (ht : ∀ a : End (⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩ :
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
      F.map a ≫ t.hom = t.hom ≫ G.map a) : Nonempty (F ≅ G) := by
  let A := Γ(X, ⊤)
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)
  let d : E.functor.obj (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) ≅ ModuleCat.of A A :=
    LinearEquiv.toModuleIso {
      toFun := MulOpposite.unop
      invFun := MulOpposite.op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := (affineQuasicoherentEquivalence X).functor.mapIso d ≪≫
    affineQuasicoherentEquivalenceUnitIso X
  exact functorIsoOfGeneratorIso
    (A := Aᵐᵒᵖ) (E.trans (affineQuasicoherentEquivalence X)) _ e F G hF hG t ht

/-- A natural transformation out of a colimit-preserving functor on the quasi-coherent modules
of an affine scheme is determined by its value on the structure sheaf. -/
private lemma affineNatTrans_ext (X : Scheme.{u}) [IsAffine X]
    {B : Type*} [Category B]
    (F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ B)
    [PreservesColimitsOfSize.{u, u} F]
    [((affineQuasicoherentEquivalence X).functor ⋙ F).PreservesEpimorphisms]
    (α β : F ⟶ G)
    (h : α.app ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩ =
      β.app ⟨SheafOfModules.unit X.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩) : α = β := by
  let E := affineQuasicoherentEquivalence X
  have he : (Functor.whiskerLeft E.functor α) = Functor.whiskerLeft E.functor β := by
    apply moduleNatTrans_ext Γ(X, ⊤)
    let e := affineQuasicoherentEquivalenceUnitIso X
    apply (cancel_mono (G.map e.hom)).1
    show α.app _ ≫ G.map e.hom = β.app _ ≫ G.map e.hom
    rw [← α.naturality, ← β.naturality, h]
  exact (Functor.whiskeringLeft _ _ B).obj E.functor |>.map_injective he

/-- The morphism of direct images attached to a natural transformation of integral transforms,
by evaluating it on the structure sheaf. -/
private noncomputable def fullPreimageHom
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    {K L : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (α : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K ⟶
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj L) :
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj ⟶
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj L.obj :=
  ((formulaFunctorUnitIso R X Y).app K.obj).inv ≫
    α.app ⟨SheafOfModules.unit X.left.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≫
    ((formulaFunctorUnitIso R X Y).app L.obj).hom

/-- The morphism of direct images attached to a natural transformation of integral transforms
commutes with the action of the global functions of `X`. -/
private lemma fullPreimageHom_smul
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    {K L : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (α : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K ⟶
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj L)
    (a : Γ(X.left, ⊤)) :
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          (sectionScalar (pullback X.hom Y.hom)
            ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫
        fullPreimageHom R X Y α =
      fullPreimageHom R X Y α ≫
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          (sectionScalar (pullback X.hom Y.hom)
            ((pullback.fst X.hom Y.hom).appTop a) L.obj) := by
  let O : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.left.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩
  let F := (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
    formulaFunctor R X Y
  let e := formulaFunctorUnitIso R X Y
  let a₀ : O ⟶ O := ObjectProperty.homMk (sectionScalar X.left a O.obj)
  apply conjugate_commutes (e.app K.obj) (e.app L.obj)
    ((F.obj K).map a₀) ((F.obj L).map a₀)
  · rw [show (e.app K.obj).hom = (integralTransformUnitIso R X Y K.obj).hom from
      formulaFunctorUnitIso_hom_app R X Y K.obj]
    exact integralTransformUnitIso_sectionScalar R X Y K.obj a
  · rw [show (e.app L.obj).hom = (integralTransformUnitIso R X Y L.obj).hom from
      formulaFunctorUnitIso_hom_app R X Y L.obj]
    exact integralTransformUnitIso_sectionScalar R X Y L.obj a
  · exact α.naturality a₀

/-- The morphism of direct images attached to a natural transformation of integral transforms
is the conjugate of its value on the structure sheaf. -/
private lemma fullPreimageHom_def
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    {K L : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (α : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K ⟶
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj L) :
    fullPreimageHom R X Y α =
      ((formulaFunctorUnitIso R X Y).app K.obj).inv ≫
        α.app ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≫
        ((formulaFunctorUnitIso R X Y).app L.obj).hom := rfl

attribute [local irreducible] fullPreimageHom

/-- The morphism over the direct image of the structure sheaf of `X ×_R Y` underlying a
natural transformation of integral transforms. -/
private noncomputable def fullPreimageLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    {K L : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (α : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K ⟶
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj L) :
    (pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj K.obj ⟶
      (pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj L.obj :=
  liftRestrictScalarsHom (pullback.snd X.hom Y.hom).toRingCatSheafHom
    ((pushforwardModules (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj K.obj)
    ((pushforwardModules (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj L.obj)
    (fullPreimageHom R X Y α)
    (fun U hU r x => affine_pushforward_map_smul R X Y
      ((pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj K.obj)
      ((pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj L.obj) (fullPreimageHom R X Y α) U hU
      (fun a x => congrArg (fun k => (k.val.app (.op U)).hom x)
        (fullPreimageHom_smul R X Y α a)) r x)

/-- Direct image along the second projection turns multiplication by the pullback of a global
function on `X` into a given action on the target, under an identification coming from an
isomorphism over the direct image of the structure sheaf. -/
private lemma pushforward_sectionScalar_intertwine
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (M : Y.left.Modules) (ρ : Γ(X.left, ⊤) →+* End M)
    (N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf))
    (e : (SheafOfModules.restrictScalars
      (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅ M)
    (he : ∀ (U : Y.left.Opensᵒᵖ) (a : Γ(X.left, ⊤)) (x : N.val.obj U),
      e.hom.val.app U (sectionToProduct R X Y U a • x) =
        (ρ a).val.app U (e.hom.val.app U x))
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (d : (pushforwardModules (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj K.obj ≅ N)
    (a : Γ(X.left, ⊤)) :
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          (sectionScalar (pullback X.hom Y.hom)
            ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫
        ((SheafOfModules.restrictScalars
          (pullback.snd X.hom Y.hom).toRingCatSheafHom).mapIso d ≪≫ e).hom =
      ((SheafOfModules.restrictScalars
        (pullback.snd X.hom Y.hom).toRingCatSheafHom).mapIso d ≪≫ e).hom ≫ ρ a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show e.hom.val.app U (d.hom.val.app U
    (sectionToProduct R X Y U a •
      (show ((pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj K.obj).val.obj U from x))) =
      (ρ a).val.app U (e.hom.val.app U (d.hom.val.app U x))
  rw [(d.hom.val.app U).hom.map_smul]
  exact he U a (d.hom.val.app U x)

/-- The structure sheaf of a scheme, as a quasi-coherent module. -/
private abbrev unitQcoh (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ⟨SheafOfModules.unit X.ringCatSheaf,
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩

/-- Restricting scalars along the second projection undoes the lift over the direct image of
the structure sheaf of a natural transformation's value on the structure sheaf. -/
private lemma restrictScalars_map_fullPreimageLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    {K L : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (α : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K ⟶
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj L) :
    (SheafOfModules.restrictScalars (pullback.snd X.hom Y.hom).toRingCatSheafHom).map
        (fullPreimageLift R X Y α) = fullPreimageHom R X Y α :=
  restrictScalars_map_liftRestrictScalarsHom _ _ _ _ _

/-- For `X` affine, the kernel-functorial formula is full in the kernel.  A natural
transformation is determined by its value on the structure sheaf, where the formula is direct
image along the affine second projection; that value is linear over the direct image of the
structure sheaf of `X ×_R Y`, so Tag 01SB produces a morphism of kernels inducing it. -/
private lemma formulaFunctor_full
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      formulaFunctor R X Y).Full := by
  have hq : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  refine ⟨fun {K L} α => ?_⟩
  let G := Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward
    (pullback.snd X.hom Y.hom)
  have hGe : G.IsEquivalence :=
    Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward
      (pullback.snd X.hom Y.hom)
  let phi : G.obj K ⟶ G.obj L := ObjectProperty.homMk (fullPreimageLift R X Y α)
  let k : K ⟶ L := G.preimage phi
  have h2 : (pushforwardModules (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).map k.hom = (G.map k).hom := rfl
  have h3 : G.map k = phi := G.map_preimage phi
  have h4 : phi.hom = fullPreimageLift R X Y α := rfl
  have hk : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map k.hom =
      fullPreimageHom R X Y α := by
    rw [pushforward_map_eq_restrictScalars_map (pullback.snd X.hom Y.hom) k.hom, h2, h3, h4,
      restrictScalars_map_fullPreimageLift R X Y α]
  refine ⟨k, ?_⟩
  have hpc : PreservesColimitsOfSize.{u, u}
      (((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
        formulaFunctor R X Y).obj K) :=
    @preservesColimits_of_natIso _ _ _ _ _ _
      (formulaFunctorObjIso R X Y K.obj).symm
      (integralTransformFormula_preservesColimits R X Y K)
  apply affineNatTrans_ext X.left _ _
  apply (cancel_mono ((formulaFunctorUnitIso R X Y).app L.obj).hom).1
  have hn := (formulaFunctorUnitIso R X Y).hom.naturality k.hom
  change ((formulaFunctor R X Y).map k.hom).app (unitQcoh X.left) ≫
      (formulaFunctorUnitIso R X Y).hom.app L.obj =
    (formulaFunctorUnitIso R X Y).hom.app K.obj ≫
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map k.hom at hn
  show ((formulaFunctor R X Y).map k.hom).app (unitQcoh X.left) ≫
      (formulaFunctorUnitIso R X Y).hom.app L.obj =
    α.app (unitQcoh X.left) ≫ (formulaFunctorUnitIso R X Y).hom.app L.obj
  refine hn.trans ?_
  refine (congrArg (fun z => (formulaFunctorUnitIso R X Y).hom.app K.obj ≫ z)
    (hk.trans (fullPreimageHom_def R X Y α))).trans ?_
  simp

/-- The action of the global functions of `X` on the value at the structure sheaf of an
`R`-linear right exact functor, through the functor's additivity. -/
private noncomputable def valueAction
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory) :
    Γ(X.left, ⊤) →+* End (C := Y.left.Modules) ((F.obj.obj (unitQcoh X.left)).obj) :=
  have : F.obj.Additive := F.property.1.1
  (additiveMapEnd (F.obj ⋙ (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι)
      (unitQcoh X.left)).comp
    (quasicoherentSectionScalarRingHom X.left (unitQcoh X.left))

/-- On global functions pulled back from the base, the action at the structure sheaf is
multiplication by the corresponding global function of `Y`. -/
private lemma valueAction_base
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory)
    (r : Γ(Spec (.of R), ⊤)) :
    valueAction R X Y F (X.hom.appTop r) =
      sectionScalar Y.left (Y.hom.appTop r) ((F.obj.obj (unitQcoh X.left)).obj) := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) :=
    AlgebraicGeometry.modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) :=
    AlgebraicGeometry.modulesLinear R Y
  let : Linear R Y.left.Modules := AlgebraicGeometry.modulesLinear R Y
  have hadd : F.obj.Additive := F.property.1.1
  have hlin : F.obj.Linear R := F.property.1.2
  let F0 := F.obj ⋙ (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
  obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2 r
  show F0.map (quasicoherentSectionScalarRingHom X.left (unitQcoh X.left)
    (X.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) = _
  refine (congrArg F0.map (quasicoherentSectionScalar_base R X r (unitQcoh X.left))).trans ?_
  refine (F0.map_smul r (𝟙 (unitQcoh X.left))).trans ?_
  refine (congrArg (fun z => r • z)
    (CategoryTheory.Functor.map_id F0 (unitQcoh X.left))).trans ?_
  exact (sectionScalar_base R Y r ((F.obj.obj (unitQcoh X.left)).obj)).symm

/-- A quasi-coherent module over the direct image of the structure sheaf of `X ×_R Y` along the
second projection is the direct image of a quasi-coherent module on `X ×_R Y`. -/
private lemma exists_pushforwardModules_iso
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf)) (hN : N.IsQuasicoherent) :
    ∃ K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory,
      Nonempty ((pushforwardModules (pullback.snd X.hom Y.hom).base
        (pullback X.hom Y.hom).ringCatSheaf).obj K.obj ≅ N) := by
  have hq : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  let P := Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward
    (pullback.snd X.hom Y.hom)
  have hPe : P.IsEquivalence :=
    Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward
      (pullback.snd X.hom Y.hom)
  exact ⟨P.objPreimage ⟨N, hN⟩, ⟨(SheafOfModules.isQuasicoherent
    (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf)).ι.mapIso (P.objObjPreimageIso ⟨N, hN⟩)⟩⟩

/-- A module over the direct image of the structure sheaf of `X ×_R Y` whose scalar restriction
is quasi-coherent is itself quasi-coherent, the second projection being affine. -/
private lemma isQuasicoherent_of_restrictScalars_iso
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf))
    (M : (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory)
    (e : (SheafOfModules.restrictScalars
      (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅ M.obj) :
    N.IsQuasicoherent := by
  have hq : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  exact (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff
      (pullback.snd X.hom Y.hom) N).mp
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).prop_of_iso e.symm M.property)

/-- The direct image of a quasi-coherent kernel identified with the value of `F` at the
structure sheaf, equivariantly for the global functions of `X`. -/
private lemma exists_iso_intertwining_valueAction
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory)
    (N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf))
    (e : (SheafOfModules.restrictScalars (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅
      (F.obj.obj (unitQcoh X.left)).obj)
    (he : ∀ (U : Y.left.Opensᵒᵖ) (a : Γ(X.left, ⊤)) (x : N.val.obj U),
      e.hom.val.app U (sectionToProduct R X Y U a • x) =
        (valueAction R X Y F a).val.app U (e.hom.val.app U x))
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (d : (pushforwardModules (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf).obj K.obj ≅ N) :
    ∃ e' : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj ≅
        (F.obj.obj (unitQcoh X.left)).obj,
      ∀ a : Γ(X.left, ⊤),
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
            (sectionScalar (pullback X.hom Y.hom)
              ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫ e'.hom =
          e'.hom ≫ valueAction R X Y F a :=
  ⟨(SheafOfModules.restrictScalars
      (pullback.snd X.hom Y.hom).toRingCatSheafHom).mapIso d ≪≫ e,
    fun a => pushforward_sectionScalar_intertwine R X Y _ (valueAction R X Y F) N e he K d a⟩

/-- A module over the direct image of the structure sheaf of `X ×_R Y` carrying the action of
the global functions of `X` comes from a quasi-coherent kernel. -/
private lemma exists_kernel_of_pushforwardModule
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory)
    (N : SheafOfModules.{u} (pushforwardRing (pullback.snd X.hom Y.hom).base
      (pullback X.hom Y.hom).ringCatSheaf))
    (e : (SheafOfModules.restrictScalars (pullback.snd X.hom Y.hom).toRingCatSheafHom).obj N ≅
      (F.obj.obj (unitQcoh X.left)).obj)
    (he : ∀ (U : Y.left.Opensᵒᵖ) (a : Γ(X.left, ⊤)) (x : N.val.obj U),
      e.hom.val.app U (sectionToProduct R X Y U a • x) =
        (valueAction R X Y F a).val.app U (e.hom.val.app U x)) :
    ∃ K : (SheafOfModules.isQuasicoherent
        (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory,
      ∃ e' : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj ≅
        (F.obj.obj (unitQcoh X.left)).obj,
      ∀ a : Γ(X.left, ⊤),
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
            (sectionScalar (pullback X.hom Y.hom)
              ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫ e'.hom =
          e'.hom ≫ valueAction R X Y F a := by
  obtain ⟨K, ⟨d⟩⟩ := exists_pushforwardModules_iso R X Y N
    (isQuasicoherent_of_restrictScalars_iso R X Y N (F.obj.obj (unitQcoh X.left)) e)
  exact ⟨K, exists_iso_intertwining_valueAction R X Y F N e he K d⟩

/-- The value at the structure sheaf of an `R`-linear right exact functor is the direct image
of a quasi-coherent kernel, compatibly with the action of the global functions of `X`. -/
private lemma exists_kernel_of_valueAction
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory) :
    ∃ K : (SheafOfModules.isQuasicoherent
        (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory,
      ∃ e : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj ≅
        (F.obj.obj (unitQcoh X.left)).obj,
      ∀ a : Γ(X.left, ⊤),
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
            (sectionScalar (pullback X.hom Y.hom)
              ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫ e.hom =
          e.hom ≫ valueAction R X Y F a := by
  obtain ⟨N, e, he⟩ := exists_pushforwardModule_of_sectionAction R X Y
    ((F.obj.obj (unitQcoh X.left)).obj) (valueAction R X Y F) (valueAction_base R X Y F)
  exact exists_kernel_of_pushforwardModule R X Y F N e he

/-- The identification of the integral transform at the structure sheaf with the value of the
functor there is equivariant for the endomorphisms of the structure sheaf. -/
private lemma integralTransformUnitIso_trans_intertwine
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory)
    {K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory}
    (e : (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj ≅
      (F.obj.obj (unitQcoh X.left)).obj)
    (hs : ∀ a : Γ(X.left, ⊤),
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
          (sectionScalar (pullback X.hom Y.hom)
            ((pullback.fst X.hom Y.hom).appTop a) K.obj) ≫ e.hom =
        e.hom ≫ valueAction R X Y F a)
    (a : unitQcoh X.left ⟶ unitQcoh X.left) :
    (AlgebraicGeometry.integralTransformFormula R X Y K.obj).map a ≫
        (integralTransformUnitIso R X Y K.obj ≪≫ e).hom =
      (integralTransformUnitIso R X Y K.obj ≪≫ e).hom ≫
        (F.obj ⋙ (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι).map a := by
  obtain ⟨b, hb⟩ := sectionScalar_unit_surjective X.left a.hom
  have hb' : ObjectProperty.homMk (sectionScalar X.left b (unitQcoh X.left).obj) = a :=
    ObjectProperty.hom_ext _ hb
  subst a
  show (AlgebraicGeometry.integralTransformFormula R X Y K.obj).map
        (ObjectProperty.homMk
          (sectionScalar X.left b (SheafOfModules.unit X.left.ringCatSheaf))) ≫
      ((integralTransformUnitIso R X Y K.obj).hom ≫ e.hom) =
    ((integralTransformUnitIso R X Y K.obj).hom ≫ e.hom) ≫ valueAction R X Y F b
  exact comp_commutes_of_commutes (integralTransformUnitIso_sectionScalar R X Y K.obj b) (hs b)

/-- Every `R`-linear, right exact functor commuting with arbitrary direct sums is the integral
transform of a quasi-coherent kernel. -/
private lemma exists_kernel_of_rightExactLinearCoproductFunctor
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory) :
    ∃ K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory,
      Nonempty (F.obj ≅ quasicoherentIntegralTransform R X Y K) := by
  have hrex : PreservesFiniteColimits F.obj := F.property.2.1
  let Q := SheafOfModules.isQuasicoherent Y.left.ringCatSheaf
  have hQcol : PreservesColimitsOfSize.{u, u} Q.ι := preservesColimits_quasicoherentIota Y.left
  have hQrex : PreservesFiniteColimits Q.ι := preservesFiniteColimits_quasicoherentIota Y.left
  let F0 := F.obj ⋙ Q.ι
  have hF0rex : PreservesFiniteColimits F0 := comp_preservesFiniteColimits _ _
  obtain ⟨K, e, hs⟩ := exists_kernel_of_valueAction R X Y F
  let G := AlgebraicGeometry.integralTransformFormula R X Y K.obj
  have hGcol : PreservesColimitsOfSize.{u, u} G :=
    integralTransformFormula_preservesColimits R X Y K
  have hGrex : PreservesFiniteColimits G := inferInstance
  have hF0rex' : PreservesFiniteColimits
      (C := (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory)
      (D := Y.left.Modules) F0 := hF0rex
  have hF0dis : ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (C := (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory)
      (D := Y.left.Modules) F0 := fun I => by
    have := F.property.2.2 I
    exact inferInstanceAs (PreservesColimitsOfShape (Discrete I) (F.obj ⋙ Q.ι))
  obtain ⟨i⟩ := @affineFunctorIsoOfUnitIso X.left _ _ _ _ _ _ G F0 hGrex hF0rex'
    (fun _ => inferInstance) hF0dis (integralTransformUnitIso R X Y K.obj ≪≫ e)
    (integralTransformUnitIso_trans_intertwine R X Y F e hs)
  exact ⟨K, ⟨((Functor.whiskeringRight _ _ _).obj Q.ι).preimageIso
    (i.symm ≪≫ (AlgebraicGeometry.quasicoherentIntegralTransformData R X Y K).comparison.symm)⟩⟩

end AlgebraicGeometry.IntegralTransformQcoh

namespace AlgebraicGeometry

open IntegralTransformQcoh

/-- The integral transform of Tag 0FZB, as a functor of its kernel: a morphism of
quasi-coherent kernels on `X ×_R Y` induces a natural transformation of integral
transforms. -/
noncomputable def integralTransformQcohFunctor
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
  liftFunctorAlongFullyFaithful
    ((SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).ι ⋙ formulaFunctor R X Y)
    ((Functor.whiskeringRight _ _ _).obj
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι)
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight _)
    (quasicoherentIntegralTransform R X Y)
    (comparisonData R X Y)

/-- After forgetting quasi-coherence of the values, the kernel-functorial integral transform
is the pullback--tensor--pushforward formula, naturally in the kernel. -/
noncomputable def integralTransformQcohFunctorComparison
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    integralTransformQcohFunctor R X Y ⋙
        (Functor.whiskeringRight
          (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory
          (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory
          Y.left.Modules).obj (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent
        (pullback X.hom Y.hom).ringCatSheaf).ι ⋙ formulaFunctor R X Y :=
  liftFunctorAlongFullyFaithfulIso
    ((SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).ι ⋙ formulaFunctor R X Y)
    ((Functor.whiskeringRight _ _ _).obj
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι)
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight _)
    (quasicoherentIntegralTransform R X Y)
    (comparisonData R X Y)

/-- **Stacks Project, Tag 0FZD.** For `X` affine, the integral transform of a quasi-coherent
kernel on `X ×_R Y`, as a functor of the kernel, with codomain the `R`-linear right exact
functors from quasi-coherent modules on `X` to quasi-coherent modules on `Y` which commute with
arbitrary direct sums. -/
@[stacks 0FZD "the functor from quasi-coherent kernels to right exact linear functors"]
noncomputable def integralTransformQcohFunctorLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory ⥤
      (rightExactLinearCoproductFunctor R X Y).FullSubcategory :=
  ObjectProperty.lift (rightExactLinearCoproductFunctor R X Y)
    (integralTransformQcohFunctor R X Y)
    (fun K => rightExactLinearCoproductFunctor_quasicoherentIntegralTransform R X Y K)

/-- **Stacks Project, Tag 0FZD.** For `X` affine, the integral transform of a quasi-coherent
kernel on `X ×_R Y` is, on objects, the functor `F ↦ pr_{2,*}(pr_1^* F ⊗ K)` of Tag 0FZB. -/
@[stacks 0FZD "the functor sends a kernel to its integral transform"]
theorem integralTransformQcohFunctorLift_obj_obj
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    ((integralTransformQcohFunctorLift R X Y).obj K).obj =
      quasicoherentIntegralTransform R X Y K := rfl

/-- **Stacks Project, Tag 0FZD.** For `X` affine, the functor sending a quasi-coherent kernel
on `X ×_R Y` to its integral transform is faithful. -/
@[stacks 0FZD "the functor is faithful"]
theorem faithful_integralTransformQcohFunctorLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (integralTransformQcohFunctorLift R X Y).Faithful := by
  have : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      formulaFunctor R X Y).Faithful := formulaFunctor_faithful R X Y
  have : ((Functor.whiskeringRight
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory
      Y.left.Modules).obj (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι).Faithful :=
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).faithful
  have hHfaith : (integralTransformQcohFunctor R X Y).Faithful :=
    (integralTransformQcohFunctorComparison R X Y).faithful_of_comp
  constructor
  intro K L f g h
  apply hHfaith.map_injective
  exact congrArg (fun t => t.hom) h

/-- **Stacks Project, Tag 0FZD.** For `X` affine, the functor sending a quasi-coherent kernel
on `X ×_R Y` to its integral transform is full. -/
@[stacks 0FZD "the functor is full"]
theorem full_integralTransformQcohFunctorLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (integralTransformQcohFunctorLift R X Y).Full := by
  have : ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      formulaFunctor R X Y).Full := formulaFunctor_full R X Y
  have : ((Functor.whiskeringRight
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory
      Y.left.Modules).obj (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι).Faithful :=
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).faithful
  have hHfull : (integralTransformQcohFunctor R X Y).Full :=
    Functor.Full.of_comp_faithful_iso (integralTransformQcohFunctorComparison R X Y)
  constructor
  intro K L φ
  obtain ⟨f, hf⟩ := hHfull.map_surjective φ.hom
  exact ⟨f, ObjectProperty.hom_ext _ hf⟩

/-- **Stacks Project, Tag 0FZD.** For `X` affine, every `R`-linear right exact functor from
quasi-coherent modules on `X` to quasi-coherent modules on `Y` which commutes with arbitrary
direct sums is the integral transform of a quasi-coherent kernel on `X ×_R Y`. -/
@[stacks 0FZD "the functor is essentially surjective"]
theorem essSurj_integralTransformQcohFunctorLift
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (integralTransformQcohFunctorLift R X Y).EssSurj :=
  ⟨fun F => by
    obtain ⟨K, ⟨e⟩⟩ := exists_kernel_of_rightExactLinearCoproductFunctor R X Y F
    exact ⟨K, ⟨ObjectProperty.isoMk _ e.symm⟩⟩⟩

/-- **Stacks Project, Tag 0FZD.** For `X` affine, the integral transform of a quasi-coherent
kernel is an equivalence from the quasi-coherent modules on `X ×_R Y` to the `R`-linear right
exact functors from quasi-coherent modules on `X` to quasi-coherent modules on `Y` which
commute with arbitrary direct sums. -/
@[stacks 0FZD "the equivalence of categories"]
noncomputable def integralTransformQcohEquivalence
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory ≌
      (rightExactLinearCoproductFunctor R X Y).FullSubcategory :=
  have : (integralTransformQcohFunctorLift R X Y).IsEquivalence :=
    ⟨faithful_integralTransformQcohFunctorLift R X Y,
      full_integralTransformQcohFunctorLift R X Y,
      essSurj_integralTransformQcohFunctorLift R X Y⟩
  (integralTransformQcohFunctorLift R X Y).asEquivalence

/-- **Stacks Project, Tag 0FZD.** The equivalence sends a quasi-coherent kernel on `X ×_R Y`
to its integral transform `F ↦ pr_{2,*}(pr_1^* F ⊗ K)`. -/
@[stacks 0FZD "the equivalence sends a kernel to its integral transform"]
theorem integralTransformQcohEquivalence_functor_obj_obj
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    ((integralTransformQcohEquivalence R X Y).functor.obj K).obj =
      quasicoherentIntegralTransform R X Y K := rfl

end AlgebraicGeometry

end
