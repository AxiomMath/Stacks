module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials and localization at an object of the site

Let `(C, J)` be a site, let `φ : O₁ ⟶ O₂` be a homomorphism of sheaves of commutative rings on
it and let `U` be an object of `C`. Restricting a sheaf to the slice site `C/U` commutes with
forming the sheaf of relative differentials:
`Ω_{O₂/O₁}|_U ≅ Ω_{(O₂|_U)/(O₁|_U)}`, by the unique identification carrying one universal
derivation to the other.

This is the special case, at the localization morphism of topoi `j_U : Sh(C/U) ⟶ Sh(C)`, of the
statement that the inverse image along a morphism of topoi commutes with relative differentials
(`Stacks.Sheaves.RingedToposModules.inverseImageDifferentialsIso`, Stacks 08TQ). The inverse
image of `j_U` *is* restriction along the slice projection `Over.forget U`, and the two
comparisons that turn the general statement into this one are already available: on sheaves of
commutative rings `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and on sheaves of
modules `Stacks.Sheaves.ToposPullback.restrictionModuleIso`. Both are the identity on underlying
sheaves of sets; only the transported ring and module structures have to be identified with the
original ones.

## Main definitions

* `CategoryTheory.GrothendieckTopology.localizationMorphismOfTopoi`: the localization morphism of
  topoi `Sh(C/U) ⟶ Sh(C)` of a site at an object, with inverse image restriction along
  `Over.forget U`.
* `CategoryTheory.GrothendieckTopology.localizationInverseImageCommRingIso`: the inverse image of
  a sheaf of commutative rings along that morphism is its restriction to the slice.
* `AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso`: relative derivations transport
  along an isomorphism of the pair of sheaves of commutative rings they are taken relative to.
* `AlgebraicGeometry.SheafOfModules.overDifferentialsCorepresentableBy`: the restriction of
  `Ω_{O₂/O₁}` to the slice site over `U` corepresents the `O₁|_U`-derivations of `O₂|_U`.

## Main results

* `AlgebraicGeometry.SheafOfModules.overDifferentialsIso` (Stacks 04BO): the canonical
  isomorphism `Ω_{O₂/O₁}|_U ≅ Ω_{(O₂|_U)/(O₁|_U)}`.
* `AlgebraicGeometry.SheafOfModules.homEquiv_overDifferentialsIso_hom` (Stacks 04BO): that
  isomorphism is compatible with the universal derivations — it is the one whose transpose under
  the corepresentation above is the universal derivation of `Ω_{(O₂|_U)/(O₁|_U)}`.
* `SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso`: restriction of scalars along an
  isomorphism of sheaves of rings is fully faithful.
* `CategoryTheory.Functor.CorepresentableBy.compFullyFaithful`: a corepresentation of `G` by
  `F X`, for a fully faithful `F`, is a corepresentation of `F ⋙ G` by `X`.

## Implementation notes

Both sides of Stacks 04BO are sheaves of modules over one and the same sheaf of rings: the sheaf
of rings underlying `O₂|_U` is the restriction to the slice of the sheaf of rings underlying
`O₂`, on the nose, because restricting along `Over.forget U` and forgetting commutativity are
composition with functors on opposite sides of the presheaf. So the isomorphism is stated
directly, with no restriction of scalars intervening.

Restriction of scalars *is* needed inside the proof, because the comparison
`j_U^{-1}O₂ ≅ O₂|_U` is not an equality: the two have the same sections, but the ring structure
carried along `j_U^{-1}` and the original one are not the same term. The argument therefore runs
on the inverse-image side and descends: `Ω_{O₂/O₁}|_U` corepresents the derivations of `O₂|_U`
because, after restricting scalars along that comparison, it becomes
`j_U^{-1}Ω_{O₂/O₁} ≅ Ω_{j_U^{-1}O₂/j_U^{-1}O₁}`, which corepresents the derivations of
`j_U^{-1}O₂`; restriction of scalars along an isomorphism is fully faithful, so no information is
lost in that passage, and `derivationEquivOfRingDataIso` identifies the two notions of
derivation.

The sheaves of commutative rings take their values in `CommRingCat.{max u v w}` for a free
universe `w`, as in Stacks 08TQ: the topoi of the localization morphism have value category
`Type (max u v w)`, which must contain both the slice category `Over U : Type (max u v)` and the
sections, and the universe of the coefficient sheaves of modules is the same one. The object and
morphism universes of the site stay independent and the site is not assumed small.

## References

* [Stacks Project, Tag 04BO](https://stacks.math.columbia.edu/tag/04BO)
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (inverseImageDifferentialsIso)
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite derivationsFunctor
  universalDerivationOfSite corepresentableByIso)

universe w v u t u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.CorepresentableBy

/-- A corepresentation of `G` by `F X`, for a fully faithful functor `F`, is a corepresentation
of `F ⋙ G` by `X`: the bijection is that of `G` precomposed with the bijection `F` induces on
morphisms out of `X`. -/
def compFullyFaithful {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {F : A ⥤ B} {G : B ⥤ Type t} {X : A} (e : G.CorepresentableBy (F.obj X))
    (hF : F.FullyFaithful) : (F ⋙ G).CorepresentableBy X where
  homEquiv {Y} := hF.homEquiv.trans e.homEquiv
  homEquiv_comp {Y Y'} g f := by
    change e.homEquiv (F.map (f ≫ g)) = G.map (F.map g) (e.homEquiv (F.map f))
    rw [F.map_comp, e.homEquiv_comp]

end CategoryTheory.Functor.CorepresentableBy

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}} (τ : R ⟶ R') [IsIso τ]

/-- Restriction of scalars along an isomorphism `τ` of sheaves of rings is bijective on
morphisms: a morphism of sheaves of modules that is linear over `R` is linear over `R'`, because
every section of `R'` is the image of one of `R`. -/
noncomputable def restrictScalarsHomEquivOfIsIso (M N : SheafOfModules.{t} R') :
    (M ⟶ N) ≃ ((restrictScalars τ).obj M ⟶ (restrictScalars τ).obj N) :=
  haveI : Presheaf.IsLocallySurjective J τ.hom := Sheaf.isLocallySurjective_of_iso τ
  ((fullyFaithfulForget R').homEquiv (X := M) (Y := N)).trans
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective (J := J) τ.hom N.isSheaf).trans
      ((fullyFaithfulForget R).homEquiv (X := (restrictScalars τ).obj M)
        (Y := (restrictScalars τ).obj N)).symm)

/-- The bijection of `SheafOfModules.restrictScalarsHomEquivOfIsIso` is restriction of scalars
itself. -/
lemma restrictScalarsHomEquivOfIsIso_apply {M N : SheafOfModules.{t} R'} (f : M ⟶ N) :
    restrictScalarsHomEquivOfIsIso τ M N f = (restrictScalars τ).map f := rfl

/-- **Restriction of scalars along an isomorphism of sheaves of rings is fully faithful.** -/
noncomputable def fullyFaithfulRestrictScalarsOfIsIso :
    (restrictScalars.{t} τ).FullyFaithful where
  preimage {M N} f := (restrictScalarsHomEquivOfIsIso τ M N).symm f
  map_preimage {M N} f := (restrictScalarsHomEquivOfIsIso_apply τ _).symm.trans
    ((restrictScalarsHomEquivOfIsIso τ M N).apply_symm_apply f)
  preimage_map {M N} f :=
    (congrArg (restrictScalarsHomEquivOfIsIso τ M N).symm
        (restrictScalarsHomEquivOfIsIso_apply τ f)).symm.trans
      ((restrictScalarsHomEquivOfIsIso τ M N).symm_apply_apply f)

end SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Relative derivations transport along an isomorphism of the ring data.** Let `α : A ≅ A'`
and `β : P ≅ P'` be isomorphisms of sheaves of commutative rings forming a commutative square
with `g : A ⟶ P` and `g' : A' ⟶ P'`, and let `M` be a sheaf of `P'`-modules. An `A`-derivation
of `P` with values in `M` read as a sheaf of `P`-modules along `β` is the same thing as an
`A'`-derivation of `P'` with values in `M`: compose the derivation with the sections of `β`. -/
noncomputable def derivationEquivOfRingDataIso
    {A A' P P' : Sheaf J CommRingCat.{t}} (α : A ≅ A') (β : P ≅ P')
    {g : A ⟶ P} {g' : A' ⟶ P'} (hg : g ≫ β.hom = α.hom ≫ g')
    (M : _root_.SheafOfModules.{t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, t} (J := J)) P')) :
    PresheafOfModulesOfCommRing.Derivation' ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, t} J).map β.hom)).obj M).val g.hom ≃
      PresheafOfModulesOfCommRing.Derivation' M.val g'.hom := by
  have hβi : ∀ (X : Cᵒᵖ) (z : P'.obj.obj X), β.hom.hom.app X (β.inv.hom.app X z) = z :=
    fun X z ↦ congrArg (fun k : P' ⟶ P' ↦ k.hom.app X z) β.inv_hom_id
  have hβh : ∀ (X : Cᵒᵖ) (z : P.obj.obj X), β.inv.hom.app X (β.hom.hom.app X z) = z :=
    fun X z ↦ congrArg (fun k : P ⟶ P ↦ k.hom.app X z) β.hom_inv_id
  have hcomm : ∀ (X : Cᵒᵖ) (z : A.obj.obj X),
      β.hom.hom.app X (g.hom.app X z) = g'.hom.app X (α.hom.hom.app X z) :=
    fun X z ↦ congrArg (fun k : A ⟶ P' ↦ k.hom.app X z) hg
  exact
  { toFun := fun D ↦
      { d := fun {X} ↦ (D.d (X := X)).comp (β.inv.hom.app X).hom.toAddMonoidHom
        d_mul := fun {X} x y ↦ by
          change D.d (β.inv.hom.app X (x * y)) = _
          rw [map_mul (β.inv.hom.app X).hom]
          refine (D.d_mul (β.inv.hom.app X x) (β.inv.hom.app X y)).trans ?_
          change (show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, t} (J := J)) P').obj.obj X
                from β.hom.hom.app X (β.inv.hom.app X x)) •
                (show M.val.obj X from D.d (β.inv.hom.app X y)) +
              (show ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, t} (J := J)) P').obj.obj X from
                β.hom.hom.app X (β.inv.hom.app X y)) •
                (show M.val.obj X from D.d (β.inv.hom.app X x)) = _
          rw [hβi, hβi]
          rfl
        d_map := fun {X Z} f z ↦ by
          have h := congrArg (fun k ↦ k z) (β.inv.hom.naturality f)
          dsimp at h
          change D.d (β.inv.hom.app Z (P'.obj.map f z)) = _
          rw [h]
          exact D.d_map f _
        d_app := fun {X} a ↦ by
          change D.d (β.inv.hom.app X (g'.hom.app X a)) = 0
          have hα : α.hom.hom.app X (α.inv.hom.app X a) = a :=
            congrArg (fun k : A' ⟶ A' ↦ k.hom.app X a) α.inv_hom_id
          rw [← hα, ← hcomm, hβh]
          exact D.d_app _ }
    invFun := fun D ↦
      { d := fun {X} ↦ (D.d (X := X)).comp (β.hom.hom.app X).hom.toAddMonoidHom
        d_mul := fun {X} x y ↦ by
          change D.d (β.hom.hom.app X (x * y)) = _
          rw [map_mul (β.hom.hom.app X).hom]
          exact D.d_mul _ _
        d_map := fun {X Z} f z ↦ by
          have h := congrArg (fun k ↦ k z) (β.hom.hom.naturality f)
          dsimp at h
          change D.d (β.hom.hom.app Z (P.obj.map f z)) = _
          rw [h]
          exact D.d_map f _
        d_app := fun {X} a ↦ by
          change D.d (β.hom.hom.app X (g.hom.app X a)) = 0
          rw [hcomm]
          exact D.d_app _ }
    left_inv := fun D ↦ by
      ext X z
      change D.d (β.inv.hom.app X (β.hom.hom.app X z)) = D.d z
      rw [hβh]
    right_inv := fun D ↦ by
      ext X z
      change D.d (β.hom.hom.app X (β.inv.hom.app X z)) = D.d z
      rw [hβi] }

end AlgebraicGeometry.SheafOfModules

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

/-- **The localization morphism of topoi `Sh(C/U) ⟶ Sh(C)` of a site at an object `U`.** Its
inverse image is restriction along the slice projection `Over.forget U`, which is left exact
because that functor is cocontinuous, and its direct image is the right adjoint of that
restriction. This is the structure-sheaf-free form of
`AlgebraicGeometry.RingedSite.overMorphismOfTopoi`. -/
@[sga "4 III 2.4" "special case", sga "4 III 4.4" "special case", sga "4 III 5.3"]
noncomputable def localizationMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (J.over U) (Type (max u v w))) (Sheaf J (Type (max u v w))) where
  inverseImage := (Over.forget U).sheafPushforwardContinuous _ (J.over U) J
  pushforward := (Over.forget U).sheafPushforwardCocontinuous _ (J.over U) J
  adj := (Over.forget U).sheafAdjunctionCocontinuous _ (J.over U) J
  preservesFiniteLimits := inferInstance

/-- The inverse image of the localization morphism of topoi is restriction along the slice
projection. -/
lemma localizationMorphismOfTopoi_inverseImage :
    (localizationMorphismOfTopoi.{w} J U).inverseImage =
      (Over.forget U).sheafPushforwardContinuous (Type (max u v w)) (J.over U) J :=
  rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v w})]

/-- **The inverse image of a sheaf of commutative rings along the localization morphism of topoi
is its restriction to the slice site over `U`.** The sections agree on the nose and the
transported ring operations agree with the original ones. -/
noncomputable abbrev localizationInverseImageCommRingIso (O : Sheaf J CommRingCat.{max u v w}) :
    (localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O ≅ O.over U :=
  restrictionCommRingIso (J.over U) J (Over.forget U) O

/-- Restriction of scalars along the comparison
`CategoryTheory.GrothendieckTopology.localizationInverseImageCommRingIso`: it reads a sheaf of
modules over the restriction `O|_U` as a sheaf of modules over the inverse image of `O`. -/
noncomputable abbrev localizationRestrictScalars (O : Sheaf J CommRingCat.{max u v w}) :
    SheafOfModules.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (J.over U))) (O.over U)) ⥤
      SheafOfModules.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (J.over U)))
          ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O)) :=
  SheafOfModules.restrictScalars
    ((Stacks.forgetCommRingSheaf (J.over U)).map
      (localizationInverseImageCommRingIso.{w} J U O).hom)

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.SheafOfModules

open CategoryTheory.GrothendieckTopology (localizationMorphismOfTopoi
  localizationInverseImageCommRingIso localizationRestrictScalars)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  {O₁ O₂ : Sheaf J CommRingCat.{max u v w}} (φ : O₁ ⟶ O₂)

/-- The derivations of the inverse image of `φ` along the localization morphism of topoi are the
derivations of its restriction `φ|_U` to the slice site over `U`, naturally in the coefficient
sheaf of modules. -/
noncomputable def localizationDerivationsFunctorIso :
    localizationRestrictScalars.{w} J U O₂ ⋙ derivationsFunctor.{max u v w}
          ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₁)
          ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₂)
          ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.map φ) ≅
      derivationsFunctor.{max u v w} (O₁.over U) (O₂.over U)
        ((J.overPullback CommRingCat.{max u v w} U).map φ) :=
  NatIso.ofComponents
    (fun M ↦ (derivationEquivOfRingDataIso (localizationInverseImageCommRingIso.{w} J U O₁)
      (localizationInverseImageCommRingIso.{w} J U O₂)
      (restrictionCommRingIso_naturality (J.over U) J (Over.forget U) φ) M).toIso)
    (fun _ ↦ rfl)

/-- **Stacks 08TQ at the localization morphism of topoi.** Read over the inverse image of `O₂`,
the restriction of `Ω_{O₂/O₁}` to the slice site over `U` is the sheaf of relative differentials
of the inverse image of `φ`: it is that inverse image by
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, and Stacks 08TQ identifies that with
`Ω_{j_U^{-1}O₂/j_U^{-1}O₁}`. -/
noncomputable def overDifferentialsInverseImageIso :
    (localizationRestrictScalars.{w} J U O₂).obj
        ((moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w} O₁ O₂ φ).over U) ≅
      moduleOfDifferentialsOfSite.{v, max u v, max u v w, max u v w}
        ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₁)
        ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₂)
        ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.map φ) :=
  (restrictionModuleSheafIso (J.over U) J (Over.forget U)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O₂)
      (moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w} O₁ O₂ φ)).symm ≪≫
    inverseImageDifferentialsIso (localizationMorphismOfTopoi.{w} J U) φ

/-- **The restriction of `Ω_{O₂/O₁}` to the slice site over `U` corepresents the
`O₁|_U`-derivations of `O₂|_U`.** A morphism out of it is, after restricting scalars along the
comparison of the inverse image with restriction, a morphism out of
`Ω_{j_U^{-1}O₂/j_U^{-1}O₁}`, hence a `j_U^{-1}O₁`-derivation of `j_U^{-1}O₂`, hence an
`O₁|_U`-derivation of `O₂|_U`. -/
noncomputable def overDifferentialsCorepresentableBy :
    (derivationsFunctor.{max u v w} (O₁.over U) (O₂.over U)
        ((J.overPullback CommRingCat.{max u v w} U).map φ)).CorepresentableBy
      ((moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w} O₁ O₂ φ).over U) :=
  ((((derivationsFunctor.{max u v w}
            ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₁)
            ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.obj O₂)
            ((localizationMorphismOfTopoi.{w} J U).inverseImageRing.map
              φ)).corepresentableBy).ofIsoObj
          (overDifferentialsInverseImageIso.{w} J U φ)).compFullyFaithful
      (_root_.SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso
        ((Stacks.forgetCommRingSheaf (J.over U)).map
          (localizationInverseImageCommRingIso.{w} J U O₂).hom))).ofIso
    (localizationDerivationsFunctorIso.{w} J U φ)

/-- **Stacks 04BO.** For a homomorphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site
and an object `U` of that site, the restriction of the sheaf of relative differentials to the
slice site over `U` is the sheaf of relative differentials of the restrictions:
`Ω_{O₂/O₁}|_U ≅ Ω_{(O₂|_U)/(O₁|_U)}`. -/
@[stacks 04BO "the canonical isomorphism, with the object, arrow and section universes of the
site independent"]
noncomputable def overDifferentialsIso :
    (moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w} O₁ O₂ φ).over U ≅
      moduleOfDifferentialsOfSite.{v, max u v, max u v w, max u v w}
        (O₁.over U) (O₂.over U) ((J.overPullback CommRingCat.{max u v w} U).map φ) :=
  corepresentableByIso (overDifferentialsCorepresentableBy.{w} J U φ)
    (derivationsFunctor.{max u v w} (O₁.over U) (O₂.over U)
      ((J.overPullback CommRingCat.{max u v w} U).map φ)).corepresentableBy

/-- **Stacks 04BO.** The identification is the one carrying the restriction of the universal
derivation of `Ω_{O₂/O₁}` to the universal derivation of `Ω_{(O₂|_U)/(O₁|_U)}`: transposing it
along the corepresentation of
`AlgebraicGeometry.SheafOfModules.overDifferentialsCorepresentableBy` returns that universal
derivation. -/
@[stacks 04BO "compatibility with the universal derivations"]
lemma homEquiv_overDifferentialsIso_hom :
    (overDifferentialsCorepresentableBy.{w} J U φ).homEquiv
        (overDifferentialsIso.{w} J U φ).hom =
      universalDerivationOfSite.{v, max u v, max u v w, max u v w}
        (O₁.over U) (O₂.over U) ((J.overPullback CommRingCat.{max u v w} U).map φ) :=
  (overDifferentialsCorepresentableBy.{w} J U φ).homEquiv.apply_symm_apply _

end AlgebraicGeometry.SheafOfModules

end
