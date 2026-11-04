module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalenceUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.ModuleUnitTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.ModuleWeightedTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChangeStalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# From the `ULift ℤ`-linear trace to the trace of abelian sheaves

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `w` be an
integer-valued function on `X`. The trace map of [Stacks, Tag 0GKG] is constructed, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.ModuleWeightedTrace`, for sheaves of
`Λ`-modules out of a trace on the constant sheaf; the statement of the tag itself is about
abelian sheaves. At `Λ = ULift ℤ` the two worlds are the same world, the dictionary being
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence`, and this file carries the
trace across it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.forgetModWeightedTrace` — the morphism of abelian sheaves
  `f_!(f^{-1}F) ⟶ F` underlying the `ULift ℤ`-linear trace of
  `AlgebraicGeometry.SmallEtale.modWeightedTrace` on the sheaf of `ULift ℤ`-modules attached to
  an abelian sheaf `F`, read through the comparisons of the `ULift ℤ`-linear `f_!` and `f^{-1}`
  with the abelian ones.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v w

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall
attribute [local instance] modStalkMonoidal

/-- **The abelian sheaf morphism underlying the `ULift ℤ`-linear trace.** Forgetting the module
structure of the trace `f_!(f^{-1}G) ⟶ G` of
`AlgebraicGeometry.SmallEtale.modWeightedTrace` at the sheaf of `ULift ℤ`-modules `G` attached to
an abelian sheaf `F`, and reading its source through the comparisons
`AlgebraicGeometry.SmallEtale.modPullbackForget_natIso` and
`AlgebraicGeometry.SmallEtale.fShriekModForget_natIso` of the `ULift ℤ`-linear `f^{-1}` and `f_!`
with the abelian ones, gives a morphism of abelian sheaves `f_!(f^{-1}F) ⟶ F`. -/
public def forgetModWeightedTrace
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F :=
  (fShriekFunctor.{u, v} B f).map
      ((modPullbackForget_natIso.{u, v} B f).inv.app ((intModuleSheaf.{u, v} B Y).obj F)) ≫
    (fShriekModForget_natIso.{u, v} B f).inv.app
        ((modPullback.{u, v, max (u + 1) v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
          ((intModuleSheaf.{u, v} B Y).obj F)) ≫
      (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).map
        (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
          ((intModuleSheaf.{u, v} B Y).obj F))

/-- Two isomorphisms with the same forward map have the same backward map. -/
private theorem iso_inv_congr {A : Type*} [Category* A] {P Q : A} {α β : P ≅ Q}
    (h : α.hom = β.hom) : α.inv = β.inv :=
  (Iso.inv_eq_inv α β).2 h

/-- **The `ULift ℤ`-linear stalk decomposition of Stacks 0F5F forgets to the abelian one, read
backwards.** The forward direction is `AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso_forget₂`
and holds by `rfl`; the backward direction follows because an isomorphism is determined by its
forward map. -/
public theorem forget₂_map_moduleFShriekStalkIso_inv (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X (AddCommGrpCat.ULiftInt.{max (u + 1) v})) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s F).inv =
      (fShriekStalkIso.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj F)).inv := by
  exact iso_inv_congr
    (α := (forget₂ _ AddCommGrpCat).mapIso (moduleFShriekStalkIso B _ f s F))
    (β := fShriekStalkIso B f s _)
    (moduleFShriekStalkIso_forget₂.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s F)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The identification of the two `ULift ℤ`-module structures on the direct sum of the stalks
over the geometric fibre, on the summand indexed by a point of that fibre.** On underlying
abelian groups the comparison
`AlgebraicGeometry.SmallEtale.moduleFiberStalksIso` carries the summand inclusion
`AlgebraicGeometry.SmallEtale.fiberStalkOf` of the abelian direct sum to the summand inclusion
`AlgebraicGeometry.SmallEtale.modFiberStalkOf`, with the stalk read through
`AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso`. -/
public theorem forget₂_map_moduleFiberStalksIso_hom_fiberStalkOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
    (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
        (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj F).obj)) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s F).hom
        (fiberStalkOf.{u, v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj F) x z) =
      modFiberStalkOf.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s F x
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
            (x.toGeometricPoint B f s)).hom.app F z) := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  show DirectSum.congrLinearEquiv
      (fun y : GeometricFiberPoint B f s =>
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
            (y.toGeometricPoint B f s)).app F).toLinearEquiv)
      (DirectSum.of _ x z) = _
  rw [DirectSum.coe_congrLinearEquiv]
  exact DirectSum.lmap_of
    (fun y : GeometricFiberPoint B f s =>
      ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
          (y.toGeometricPoint B f s)).app F).toLinearEquiv.toLinearMap) x z


section Transport

/-- Composing on the right is compatible with equality. -/
private theorem comp_congr_left {A : Type*} [Category* A] {P Q R : A} {g h : P ⟶ Q}
    (e : g = h) (k : Q ⟶ R) : g ≫ k = h ≫ k :=
  congrArg (fun m => m ≫ k) e

/-- A functor applied to equal morphisms gives equal morphisms. -/
private theorem map_congr {A A' : Type*} [Category* A] [Category* A'] (Fn : A ⥤ A')
    {P Q : A} {g h : P ⟶ Q} (e : g = h) : Fn.map g = Fn.map h :=
  congrArg _ e

/-- A functor turns a composite of three morphisms into the composite of their images. -/
private theorem map_comp₃ {A A' : Type*} [Category* A] [Category* A'] (Fn : A ⥤ A')
    {P Q R S : A} (g : P ⟶ Q) (h : Q ⟶ R) (k : R ⟶ S) :
    Fn.map g ≫ Fn.map h ≫ Fn.map k = Fn.map (g ≫ h ≫ k) := by
  rw [← Fn.map_comp, ← Fn.map_comp]

/-- An endomorphism criterion for an isomorphism: a morphism whose composite after the inverse is
the identity is the forward map. -/
private theorem eq_hom_of_inv_comp_eq_id {A : Type*} [Category* A] {P Q : A} (α : P ≅ Q)
    (g : P ⟶ Q) (h : α.inv ≫ g = 𝟙 Q) : g = α.hom :=
  ((Iso.hom_inv_id_assoc α g).symm.trans
    (congrArg (fun m => α.hom ≫ m) h)).trans (Category.comp_id _)

/-- Moving an isomorphism from one side of an equation of morphisms to the other. -/
private theorem comp_inv_eq_of_comp_hom_eq {A : Type*} [Category* A] {P Q R : A} (α : Q ≅ R)
    {g : P ⟶ Q} {h : P ⟶ R} (e : g ≫ α.hom = h) : h ≫ α.inv = g :=
  (Iso.comp_inv_eq α).2 e.symm

/-- Moving the image under a functor of an isomorphism from one side of an equation of morphisms
to the other. -/
private theorem comp_map_inv_eq {A A' : Type*} [Category* A] [Category* A'] (Fn : A ⥤ A')
    {P Q : A} (α : P ≅ Q) {R : A'} {g : R ⟶ Fn.obj P} {h : R ⟶ Fn.obj Q}
    (e : g ≫ Fn.map α.hom = h) : h ≫ Fn.map α.inv = g := by
  rw [← e, Category.assoc, ← Fn.map_comp, α.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- **The chain of six identities that compares the two readings of the stalk of an inverse
image.** All of them are identities of morphisms in one category; stated abstractly, they
compose into the statement that the composite of the six maps is the identity, which is the
shape `CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext` leaves behind. -/
private theorem comp_eq_comp_id_of_chain {A : Type*} [Category* A]
    {S₀ SY SX SFP SMX SMY SU SUm : A}
    (gV : S₀ ⟶ SY) (ai : SY ⟶ SX) (mab : SX ⟶ SFP) (r₁ : SFP ⟶ SMX) (r₂ : SMX ⟶ SMY)
    (r₃ : SMY ⟶ SY) (uA : S₀ ⟶ SU) (iU : SU ⟶ SX) (nU : SU ⟶ SUm) (iFP : SUm ⟶ SFP)
    (um : S₀ ⟶ SUm) (iMU : SUm ⟶ SMX) (iMV : S₀ ⟶ SMY)
    (hA : gV ≫ ai = uA ≫ iU) (hB : iU ≫ mab = nU ≫ iFP) (hC : iFP ≫ r₁ = iMU)
    (hD : uA ≫ nU = um) (hE : um ≫ iMU ≫ r₂ = iMV) (hF : iMV ≫ r₃ = gV) :
    gV ≫ ai ≫ mab ≫ r₁ ≫ r₂ ≫ r₃ = gV ≫ 𝟙 SY := by
  rw [Category.comp_id, reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, reassoc_of% hD,
    reassoc_of% hE, hF]

/-- Modules over the lifted integers have small products, which is what the comparison of stalks
of Stacks 03Q1 asks of the coefficient category. -/
private theorem hasProducts_moduleCatUliftInt :
    HasProducts.{u} (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v})) :=
  fun _ => ModuleCat.hasLimitsOfShape

attribute [local instance] hasProducts_moduleCatUliftInt

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The two identifications of the stalk of an inverse image agree.** On one side stands the
comparison `AlgebraicGeometry.etaleStalkSmallEtalePullObjIso` of Stacks 03Q1 for abelian sheaves;
on the other the chain which reads the stalk of `f^{-1}F` through the dictionary
`AlgebraicGeometry.SmallEtale.modPullbackForget_natIso`, identifies the two `ULift ℤ`-module
structures on it by `AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso`, applies Stacks 03Q1 for
sheaves of `ULift ℤ`-modules and comes back. The dictionary is the mate of two adjunctions, so
this is not a definitional identity.

Both sides are maps out of the stalk of the inverse image, and the equality is proved after
composing with the inverse of the abelian comparison, which turns it into an endomorphism of the
stalk of `F` at the image point; such an endomorphism is determined by its effect on germs. On
the germ of a section over a pointed étale neighbourhood `V` the comparison of Stacks 03Q1
sends — in either world, by `AlgebraicGeometry.etaleStalkSmallEtalePullObjIso_germ`, which is
stated for arbitrary coefficients — the germ of the pullback of that section to the base change
of `V`; what is left is the compatibility of the dictionary with the units of the two
inverse-image adjunctions, which is
`CategoryTheory.Sheaf.unit_comp_sheafPullbackCoefficientIso_inv_app_app`. -/
public theorem etaleStalkSmallEtalePullObjIso_hom_eq_modPullbackStalk
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricPoint X.obj) :
    (geometricPointSitePoint B X.obj X.property x).presheafFiber.map
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F)).hom ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X x).hom.app
              ((modPullback.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
                ((intModuleSheaf.{u, v} B Y).obj F))) ≫
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              ((modPullbackStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f x).app
                ((intModuleSheaf.{u, v} B Y).obj F)).hom ≫
            (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y
                (x.map (B.inclusion.map f))).inv.app
                ((intModuleSheaf.{u, v} B Y).obj F)) =
      (etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{max (u + 1) v} F).hom := by
  let : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v,
      max (u + 1) v, max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v})
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}) :=
    preservesColimitsOfSize_shrink.{u, max (u + 1) v, u, max (u + 1) v} _
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}) :=
    ⟨fun _ => inferInstance⟩
  refine eq_hom_of_inv_comp_eq_id
    (etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{max (u + 1) v} F) _ ?_
  refine (geometricPointSitePoint B Y.obj Y.property
    (x.map (B.inclusion.map f))).presheafFiber_hom_ext (P := F.obj) ?_
  intro V v
  have ha := geometricPointFiberBaseChangeEquiv_ha B f x V v
  have hab : (pullbackSectionAlongHom B f AddCommGrpCat.{max (u + 1) v} F V
          ((smallEtaleBaseChange B f).obj V) (𝟙 _) ≫
        (geometricPointSitePoint B X.obj X.property x).toPresheafFiber
          ((smallEtaleBaseChange B f).obj V)
          (geometricPointFiberBaseChangeEquiv B f x V v)
          ((abPullback.{u, v} B f).obj F).obj) ≫
      (etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{max (u + 1) v} F).hom =
    (geometricPointSitePoint B Y.obj Y.property
      (x.map (B.inclusion.map f))).toPresheafFiber V v F.obj :=
    (Category.assoc _ _ _).trans
      (etaleStalkSmallEtalePullObjIso_germ B f x AddCommGrpCat.{max (u + 1) v} F
        ⟨(smallEtaleBaseChange B f).obj V, geometricPointFiberBaseChangeEquiv B f x V v⟩
        ⟨V, v⟩ (𝟙 _) ha)
  have hmd := etaleStalkSmallEtalePullObjIso_germ B f x
    (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
    ((intModuleSheaf.{u, v} B Y).obj F)
    ⟨(smallEtaleBaseChange B f).obj V, geometricPointFiberBaseChangeEquiv B f x V v⟩
    ⟨V, v⟩ (𝟙 _) ha
  have hA := comp_inv_eq_of_comp_hom_eq
    (etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{max (u + 1) v} F) hab
  have hB := (geometricPointSitePoint B X.obj X.property x).toPresheafFiber_naturality
    ((modPullbackForget_natIso.{u, v} B f).inv.app ((intModuleSheaf.{u, v} B Y).obj F)).hom
    ((smallEtaleBaseChange B f).obj V) (geometricPointFiberBaseChangeEquiv B f x V v)
  have hC := (geometricPointSitePoint B X.obj X.property
      x).toPresheafFiber_presheafFiberCompIso_hom_app
    (F := forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
      AddCommGrpCat.{max (u + 1) v})
    ((smallEtaleBaseChange B f).obj V) (geometricPointFiberBaseChangeEquiv B f x V v)
    ((modPullback.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
      ((intModuleSheaf.{u, v} B Y).obj F)).obj
  have hCY := (geometricPointSitePoint B Y.obj Y.property
      (x.map (B.inclusion.map f))).toPresheafFiber_presheafFiberCompIso_hom_app
    (F := forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
      AddCommGrpCat.{max (u + 1) v})
    V v ((intModuleSheaf.{u, v} B Y).obj F).obj
  have hgen := CategoryTheory.Sheaf.unit_comp_sheafPullbackCoefficientIso_inv_app_app
    (smallEtaleBaseChange B f) (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}
    ((intModuleSheaf.{u, v} B Y).obj F) V
  have hD : pullbackSectionAlongHom B f AddCommGrpCat.{max (u + 1) v} F V
          ((smallEtaleBaseChange B f).obj V) (𝟙 _) ≫
        ((modPullbackForget_natIso.{u, v} B f).inv.app
          ((intModuleSheaf.{u, v} B Y).obj F)).hom.app
          (op ((smallEtaleBaseChange B f).obj V)) =
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}).map
        (pullbackSectionAlongHom B f
          (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          ((intModuleSheaf.{u, v} B Y).obj F) V ((smallEtaleBaseChange B f).obj V) (𝟙 _)) :=
    (CategoryTheory.eq_whisker
        (pullbackSectionAlongHom_id B f AddCommGrpCat.{max (u + 1) v} F V)
        (((modPullbackForget_natIso.{u, v} B f).inv.app
          ((intModuleSheaf.{u, v} B Y).obj F)).hom.app
          (op ((smallEtaleBaseChange B f).obj V)))).trans
      (hgen.trans
        (Functor.congr_map
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v})
          (pullbackSectionAlongHom_id B f
            (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            ((intModuleSheaf.{u, v} B Y).obj F) V)).symm)
  have hE := (map_comp₃
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}) _ _ _).trans
    (Functor.congr_map
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}) hmd)
  have hF := comp_map_inv_eq
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
      AddCommGrpCat.{max (u + 1) v})
    ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y
      (x.map (B.inclusion.map f))).app ((intModuleSheaf.{u, v} B Y).obj F)) hCY
  exact comp_eq_comp_id_of_chain _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hD hE hF


/-- Composing on the left is compatible with equality. -/
private theorem comp_congr_right {A : Type*} [Category* A] {P Q R : A} (g : P ⟶ Q)
    {h k : Q ⟶ R} (e : h = k) : g ≫ h = g ≫ k :=
  congrArg (fun m => g ≫ m) e

/-- A naturality square read backwards on both isomorphisms. -/
private theorem inv_comp_eq_comp_inv {A : Type*} [Category* A] {P Q R S : A}
    (α : P ≅ Q) (β : R ≅ S) {k : P ⟶ R} {m : Q ⟶ S}
    (e : k ≫ β.hom = α.hom ≫ m) : α.inv ≫ k = m ≫ β.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← e, Category.assoc, β.hom_inv_id, Category.comp_id]

/-- Rewriting a composite of two morphisms through a factorisation of the first and a
rewriting of the middle. -/
private theorem comp_assoc_rewrite {A : Type*} [Category* A] {T₀ T₁ T₂ T₃ T₄ : A}
    {m : T₀ ⟶ T₂} (b : T₀ ⟶ T₁) (c : T₁ ⟶ T₂) (d : T₂ ⟶ T₃) (p : T₁ ⟶ T₄) (q : T₄ ⟶ T₃)
    (hm : m = b ≫ c) (hcd : c ≫ d = p ≫ q) : m ≫ d = (b ≫ p) ≫ q := by
  rw [hm, Category.assoc, hcd]
  simp only [Category.assoc]

/-- Rewriting the tail of a fourfold composite against a known factorisation of its head. -/
private theorem chain_with_tail {A : Type*} [Category* A] {T₀ T₁ T₂ T₃ T₄ T₅ : A}
    (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂) (c : T₂ ⟶ T₃) (d : T₃ ⟶ T₄) (p : T₂ ⟶ T₅) (q : T₅ ⟶ T₄)
    (g : T₀ ⟶ T₅) (hcd : c ≫ d = p ≫ q) (hg : a ≫ b ≫ p = g) :
    a ≫ b ≫ c ≫ d = g ≫ q := by
  rw [hcd, ← hg]
  simp only [Category.assoc]

/-- Rewriting a composite through a factorisation of its second factor and of the two halves. -/
private theorem comp_chain_rewrite {A : Type*} [Category* A] {T₀ T₁ T₂ T₃ T₄ : A}
    {ks : T₁ ⟶ T₃} (hs : T₀ ⟶ T₁) (kv : T₁ ⟶ T₂) (kt : T₂ ⟶ T₃)
    (m : T₀ ⟶ T₄) (n : T₄ ⟶ T₂) (final : T₄ ⟶ T₃)
    (hK : ks = kv ≫ kt) (h1 : hs ≫ kv = m ≫ n) (h2 : n ≫ kt = final) :
    hs ≫ ks = m ≫ final := by
  rw [hK, ← Category.assoc, h1, Category.assoc, h2]

/-- A fourfold composite of morphisms of abelian groups, on an element. -/
private theorem comp₄_apply {T₀ T₁ T₂ T₃ T₄ : AddCommGrpCat.{w}}
    (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂) (c : T₂ ⟶ T₃) (d : T₃ ⟶ T₄) (y : T₀) :
    (a ≫ b ≫ c ≫ d) y = d (c (b (a y))) := by
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

/-- Transporting a morphism of a family across an equality of indices. -/
private theorem eqToHom_comp_family {A : Type*} [Category* A] {ι : Type*}
    (P' Q' : ι → A) (β : ∀ i, P' i ⟶ Q' i) {i j : ι} (h : i = j) :
    eqToHom (congrArg P' h) ≫ β j = β i ≫ eqToHom (congrArg Q' h) := by
  cases h
  simp

/-- Forgetting the module structure of a morphism of `ULift ℤ`-modules does not change the map
of underlying sets. -/
private theorem forget₂_map_apply {R : Type w} [Ring R] {M N : ModuleCat.{w} R} (φ : M ⟶ N)
    (y : (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj M) :
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map φ y = φ y :=
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Moving a stalk across an equality of geometric points commutes with the comparison of the
two `ULift ℤ`-module structures on it.** Both sides are the transport of the comparison along the
equality, read on underlying abelian groups. -/
public theorem forget₂_map_eqToHom_comp_moduleEtaleStalkIso_inv_app (S : B.Scheme)
    {t t' : GeometricPoint S.obj} (h : t = t')
    (G : ModuleSheaf.{u, v, max (u + 1) v} B S (AddCommGrpCat.ULiftInt.{max (u + 1) v})) :
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          (eqToHom (congrArg (fun r => (modStalkFunctor.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S r).obj G) h)) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t').inv.app G) =
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S t).inv.app G) ≫
        eqToHom (congrArg (fun r => etaleStalk B S.obj S.property r
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B S
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj G).obj) h) :=
  (CategoryTheory.eq_whisker (CategoryTheory.eqToHom_map
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}) _) _).trans
    (eqToHom_comp_family
      (fun r => (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}).obj
        ((modStalkFunctor.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S r).obj G))
      (fun r => etaleStalk B S.obj S.property r
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj G).obj)
      (fun r => (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) S r).inv.app G)) h)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Stacks 03Q1 above a point of the geometric fibre: the module-world and abelian-world
identifications agree.** This is
`AlgebraicGeometry.SmallEtale.etaleStalkSmallEtalePullObjIso_hom_eq_modPullbackStalk` at the
geometric point of `X` attached to a point `x̄` of the geometric fibre above `ȳ`, with the two
transports along the equality `f(x̄) = ȳ` of
`AlgebraicGeometry.SmallEtale.toGeometricPoint_map` matched by
`AlgebraicGeometry.SmallEtale.forget₂_map_eqToHom_comp_moduleEtaleStalkIso_inv_app`. -/
public theorem fiberPointPullbackStalkIso_hom_eq_stalkPullbackFiberIso
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s) :
    (geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber.map
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F)).hom ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X
              (x.toGeometricPoint B f s)).hom.app
              ((modPullback.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
                ((intModuleSheaf.{u, v} B Y).obj F))) ≫
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              (stalkPullbackFiberIso.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
                ((intModuleSheaf.{u, v} B Y).obj F) x).inv ≫
            (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app
                ((intModuleSheaf.{u, v} B Y).obj F)) =
      (fiberPointPullbackStalkIso.{u, v} B f s F x).hom := by
  have hsplit : (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}).map
        (stalkPullbackFiberIso.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
          ((intModuleSheaf.{u, v} B Y).obj F) x).inv =
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((modPullbackStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f
            (x.toGeometricPoint B f s)).app ((intModuleSheaf.{u, v} B Y).obj F)).hom ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          (eqToHom (congrArg (fun r => (modStalkFunctor.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y r).obj
              ((intModuleSheaf.{u, v} B Y).obj F)) (toGeometricPoint_map B f s x))) :=
    (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
      AddCommGrpCat.{max (u + 1) v}).map_comp _ _
  have hbook := forget₂_map_eqToHom_comp_moduleEtaleStalkIso_inv_app B Y
    (toGeometricPoint_map B f s x) ((intModuleSheaf.{u, v} B Y).obj F)
  have hcd := comp_assoc_rewrite _ _ _ _ _ hsplit hbook
  exact chain_with_tail _ _ _ _ _ _ _ hcd
    (etaleStalkSmallEtalePullObjIso_hom_eq_modPullbackStalk B f F (x.toGeometricPoint B f s))

/-- **The stalk of the `ULift ℤ`-linear trace at a geometric point of `Y`, read through the
stalk decomposition of Stacks 0F5F, is the weighted sum over the geometric fibre.** This is the
characterisation of [Stacks, Tag 0GKG] in the module world, rearranged so that the three
comparisons it is read through — the decomposition
`AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso` of Stacks 0F5F, the identification
`AlgebraicGeometry.SmallEtale.moduleFiberStalksIso` of the two direct sums of stalks and the
identification `AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso` of the two module structures on
a stalk — appear on the side where the abelian statement needs them. -/
public theorem moduleFShriekStalkIso_inv_comp_moduleEtaleStalkFunctor_map_modWeightedTrace
    (w : X.obj → ℤ)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (hTr : ModHasUnitTraceStalks.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w Tr)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) :
    (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).inv ≫
        (moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map
          (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
            ((intModuleSheaf.{u, v} B Y).obj F)) =
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).hom ≫
        modWeightedTraceStalkMap.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
            ((intModuleSheaf.{u, v} B Y).obj F) s ≫
          (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F) := by
  have hmod := modHasWeightedTraceStalks_modWeightedTrace.{u, v} B
    (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w Tr hTr ((intModuleSheaf.{u, v} B Y).obj F) s
  have hΘ : ((modShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s).app
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F)) ≪≫
          moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).inv =
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).inv ≫
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).inv ≫
          (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.app
            ((fShriekMod.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((modPullback.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
                ((intModuleSheaf.{u, v} B Y).obj F))) :=
    rfl
  rw [hΘ] at hmod
  have key : (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
          ((modPullback.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
            ((intModuleSheaf.{u, v} B Y).obj F))).inv ≫
        (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.app
          ((fShriekMod.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))) ≫
          (modStalkFunctor.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map
            (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
              ((intModuleSheaf.{u, v} B Y).obj F)) =
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).hom ≫
        modWeightedTraceStalkMap.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
          ((intModuleSheaf.{u, v} B Y).obj F) s := by
    rw [← hmod]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc]
  have hnat := (moduleEtaleStalkIso.{u, v, max (u + 1) v} B
    (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).hom.naturality
      (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
        ((intModuleSheaf.{u, v} B Y).obj F))
  have hMSt := comp_inv_eq_of_comp_hom_eq
    ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
      (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).app
      ((intModuleSheaf.{u, v} B Y).obj F)) hnat
  rw [← hMSt]
  simp only [Category.assoc]
  rw [reassoc_of% key]
  rfl

/-- **The stalk of the abelian trace underlying the `ULift ℤ`-linear one**, read through the
stalk decomposition of Stacks 0F5F. Everything on the right is in the module world: the
dictionary acts on the direct sums of stalks over the geometric fibre, and what is left is the
weighted sum of
`AlgebraicGeometry.SmallEtale.modWeightedTraceStalkMap`, read back on underlying abelian
groups. -/
public theorem fShriekStalkIso_inv_comp_stalkMap_forgetModWeightedTrace (w : X.obj → ℤ)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (hTr : ModHasUnitTraceStalks.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w Tr)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) :
    (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).inv ≫
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
          (forgetModWeightedTrace.{u, v} B f Tr F).hom) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F))) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            (moduleFiberStalksIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
              ((modPullback.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
                ((intModuleSheaf.{u, v} B Y).obj F))).hom ≫
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              (modWeightedTraceStalkMap.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
                ((intModuleSheaf.{u, v} B Y).obj F) s) ≫
            (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app
                ((intModuleSheaf.{u, v} B Y).obj F)) := by
  have hsplit : forgetModWeightedTrace.{u, v} B f Tr F =
      (fShriekFunctor.{u, v} B f).map
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F)) ≫
        (forgetModuleSheaf.{u, v, max (u + 1) v} B Y
            (AddCommGrpCat.ULiftInt.{max (u + 1) v})).map
          (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
            ((intModuleSheaf.{u, v} B Y).obj F)) :=
    CategoryTheory.whisker_eq _ (Category.id_comp _)
  have hK : colim.map (Functor.whiskerLeft
        (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op
        (forgetModWeightedTrace.{u, v} B f Tr F).hom) =
      (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          ((fShriekFunctor.{u, v} B f).map
            ((modPullbackForget_natIso.{u, v} B f).inv.app
              ((intModuleSheaf.{u, v} B Y).obj F))).hom ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B Y
              (AddCommGrpCat.ULiftInt.{max (u + 1) v})).map
            (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
              ((intModuleSheaf.{u, v} B Y).obj F))).hom :=
    (congrArg (fun φ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F =>
        colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op φ.hom))
        hsplit).trans
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map_comp _ _)
  have h1 := (inv_comp_eq_comp_inv
      (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F))
      (fShriekStalkIso.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
          ((modPullback.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
            ((intModuleSheaf.{u, v} B Y).obj F))))
      (fShriekStalkIso_natural.{u, v} B f s
        ((modPullbackForget_natIso.{u, v} B f).inv.app
          ((intModuleSheaf.{u, v} B Y).obj F)))).trans
    (CategoryTheory.whisker_eq _
      (forget₂_map_moduleFShriekStalkIso_inv B f s
        ((modPullback.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
          ((intModuleSheaf.{u, v} B Y).obj F))).symm)
  have h2 : (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          (moduleFShriekStalkIso.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
            ((modPullback.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
              ((intModuleSheaf.{u, v} B Y).obj F))).inv ≫
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
            AddCommGrpCat.{max (u + 1) v}).map
          ((moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).map
            (modWeightedTrace.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f Tr
              ((intModuleSheaf.{u, v} B Y).obj F))) =
      (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
              AddCommGrpCat.{max (u + 1) v}).map
            (moduleFiberStalksIso.{u, v, max (u + 1) v} B
              (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f s
              ((modPullback.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
                ((intModuleSheaf.{u, v} B Y).obj F))).hom ≫
          (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              (modWeightedTraceStalkMap.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
                ((intModuleSheaf.{u, v} B Y).obj F) s) ≫
            (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
                AddCommGrpCat.{max (u + 1) v}).map
              ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B
                (AddCommGrpCat.ULiftInt.{max (u + 1) v}) Y s).inv.app
                ((intModuleSheaf.{u, v} B Y).obj F)) :=
    (((forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
        AddCommGrpCat.{max (u + 1) v}).map_comp _ _).symm.trans
      (Functor.congr_map
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v})
        (moduleFShriekStalkIso_inv_comp_moduleEtaleStalkFunctor_map_modWeightedTrace
          B f w Tr hTr F s))).trans
      (map_comp₃
        (forget₂ (ModuleCat.{max (u + 1) v} (AddCommGrpCat.ULiftInt.{max (u + 1) v}))
          AddCommGrpCat.{max (u + 1) v}) _ _ _).symm
  exact comp_chain_rewrite _ _ _ _ _ _ hK h1 h2

/-- **Stacks 0GKG for abelian sheaves, from the `ULift ℤ`-linear statement.** The morphism of
abelian sheaves underlying the `ULift ℤ`-linear trace has the behaviour on geometric stalks which
characterises the trace of [Stacks, Tag 0GKG], as soon as the trace on the constant sheaf it is
built from has it. -/
public theorem hasWeightedTraceStalks_forgetModWeightedTrace (w : X.obj → ℤ)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (hTr : ModHasUnitTraceStalks.{u, v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w Tr)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    HasWeightedTraceStalks.{u, v} B f w F (forgetModWeightedTrace.{u, v} B f Tr F) := by
  refine hasWeightedTraceStalks_of_fiberStalkOf.{u, v} B f w F _ ?_
  intro s x z
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (fShriekStalkIso_inv_comp_stalkMap_forgetModWeightedTrace B f w Tr hTr F s) _) ?_
  refine Eq.trans (comp₄_apply _ _ _ _ _) ?_
  have e1 : (AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v} B f s
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F))))
        (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z) =
      fiberStalkOf.{u, v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X
          (AddCommGrpCat.ULiftInt.{max (u + 1) v})).obj
          ((modPullback.{u, v, max (u + 1) v} B
            (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
            ((intModuleSheaf.{u, v} B Y).obj F))) x
        ((geometricPointSitePoint B X.obj X.property
          (x.toGeometricPoint B f s)).presheafFiber.map
          ((modPullbackForget_natIso.{u, v} B f).inv.app
            ((intModuleSheaf.{u, v} B Y).obj F)).hom z) :=
    fiberStalksMap_fiberStalkOf.{u, v} B f s
      ((modPullbackForget_natIso.{u, v} B f).inv.app ((intModuleSheaf.{u, v} B Y).obj F)) x z
  have e2 := forget₂_map_moduleFiberStalksIso_hom_fiberStalkOf B f s
    ((modPullback.{u, v, max (u + 1) v} B (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
      ((intModuleSheaf.{u, v} B Y).obj F)) x
    ((geometricPointSitePoint B X.obj X.property
      (x.toGeometricPoint B f s)).presheafFiber.map
      ((modPullbackForget_natIso.{u, v} B f).inv.app
        ((intModuleSheaf.{u, v} B Y).obj F)).hom z)
  have e3 := fun a : (modStalkFunctor.{u, v, max (u + 1) v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) X (x.toGeometricPoint B f s)).obj
        ((modPullback.{u, v, max (u + 1) v} B
          (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f).obj
          ((intModuleSheaf.{u, v} B Y).obj F)) =>
    (modWeightedTraceStalkMap_modFiberStalkOf.{u, v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
        ((intModuleSheaf.{u, v} B Y).obj F) s x a).trans
      (modWeightedTraceStalkSummand_apply.{u, v} B
        (AddCommGrpCat.ULiftInt.{max (u + 1) v}) f w
        ((intModuleSheaf.{u, v} B Y).obj F) s x a)
  have e5 := ConcreteCategory.congr_hom
    (fiberPointPullbackStalkIso_hom_eq_stalkPullbackFiberIso B f F s x) z
  erw [e1, e2, e3 _, map_zsmul]
  refine congrArg _ ?_
  exact (comp₄_apply _ _ _ _ z).symm.trans e5

/-- **[Stacks, Tag 0GKG].** For every abelian sheaf `F` on the small étale site of `Y` there is a
morphism `f_!(f^{-1}F) ⟶ F` whose effect on every geometric stalk is the weighted sum over the
geometric fibre. It is the morphism of abelian sheaves underlying the `ULift ℤ`-linear trace of
`AlgebraicGeometry.SmallEtale.modWeightedTrace`, built from the trace
`AlgebraicGeometry.SmallEtale.modUnitTrace` on the constant sheaf, which has the required
behaviour on stalks by
`AlgebraicGeometry.SmallEtale.modHasUnitTraceStalks_modUnitTrace`. Together with
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` this is the trace map of the tag. -/
@[sga "4 IX 5.1" "more general"]
public theorem exists_hasWeightedTraceStalks {w : X.obj → ℤ}
    (hw : IsWeighting (B.inclusion.map f) w)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    ∃ τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
      HasWeightedTraceStalks.{u, v} B f w F τ :=
  ⟨forgetModWeightedTrace.{u, v} B f (modUnitTrace.{u, v} B f hw) F,
    hasWeightedTraceStalks_forgetModWeightedTrace B f w (modUnitTrace.{u, v} B f hw)
      (modHasUnitTraceStalks_modUnitTrace.{u, v} B f hw) F⟩

end Transport

end AlgebraicGeometry.SmallEtale

end
