module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleFiniteSupport
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorSections

/-!
# The projection-formula recipe over one test object is `Λ`-linear

Let `f : X ⟶ Y` be a morphism of a big étale site, let `Λ` be a commutative ring, let `F` be a
sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. For a section `t` of `G` over a test
object `V`, `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom` is the recipe
`(Z, s) ↦ (Z, s ⊗ f^{-1}t)` of [Stacks, Tag 0GKF] as a map of abelian groups
`f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)`. Both groups are now `Λ`-modules, by
`AlgebraicGeometry.SmallEtale.modFiniteSupportPresheaf`, and this file proves that the recipe is
`Λ`-linear for those structures.

With the additivity and `Λ`-balancedness of the recipe in `t`, already proved in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorSections`, this is what makes the
recipe extend over `f_{p!}F(V) ⊗_Λ G(V)`.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportPushforward_map_app` — the action of `f_{p!}` on a
  morphism of abelian sheaves, read over one test object, is the map of colimits induced by the
  action on supported sections. This is
  `AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec.map_sheaf` with the colimit
  generators eliminated.
* `AlgebraicGeometry.SmallEtale.tensorSupportedSectionsHom_comp_scalar` — tensoring a supported
  section with a fixed section is `Λ`-linear in the supported section.
* `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_scalar` — **the recipe commutes
  with multiplication by a scalar** on the colimits of supported sections.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorHom` — **the recipe as a morphism of
  `Λ`-modules** `f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)`.

## Implementation notes

The values of `AlgebraicGeometry.SmallEtale.modFiniteSupportPresheaf` are those of the opaque
`AlgebraicGeometry.SmallEtale.finiteSupportPushforward`, which are the colimits of supported
sections only up to the propositional equality
`AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec.obj_eq`. So the `Λ`-linear map is
assembled by conjugating the colimit-level map with those `eqToHom`s, and the scalar actions are
compared through `finiteSupportPushforward_map_app`.

Local quasi-finiteness of `f` is needed only because `finiteSupportPushforward` is stated for a
locally quasi-finite morphism; the recipe itself needs no hypothesis on `f`.

Nothing here carries a `stacks` attribute: this is one input to [Stacks, Tag 0GKF] and not that
tag, whose comparison map of sheaves is still not constructed — see the "What is not done" note
of `StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorSections`.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v

section MapApp

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V))

/-- **The action of `f_{p!}` on a morphism of abelian sheaves over one test object.** It is the
map of colimits induced by the action of that morphism on supported sections, transported along
the identification of the values of `f_{p!}` with those colimits. -/
public theorem finiteSupportPushforward_map_app
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}} (φ : F ⟶ G)
    (V : SmallEtale B Y.obj Y.property) :
    ((finiteSupportPushforward.{u, v} B f hsmall).1.map φ).app (op V) =
      letI := hsmall V
      eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq F V) ≫
        colim.map (finiteSupportDiagramMap B f φ V) ≫
          eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq G V).symm := by
  let := hsmall V
  have h :
      eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq F V).symm ≫
          ((finiteSupportPushforward.{u, v} B f hsmall).1.map φ).app (op V) ≫
            eqToHom ((finiteSupportPushforward.{u, v} B f hsmall).2.obj_eq G V) =
        colim.map (finiteSupportDiagramMap B f φ V) := by
    refine colimit.hom_ext fun E => ?_
    rw [(finiteSupportPushforward.{u, v} B f hsmall).2.map_sheaf φ V E, colimit.ι_map]
    rfl
  rw [← h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id]

end MapApp

section Tensor

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **Tensoring a supported section with a fixed section is `Λ`-linear in the supported
section.** -/
public theorem tensorSupportedSectionsHom_comp_scalar
    (F H : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (W : SmallEtale B X.obj X.property)
    (h : H.obj.obj (op W)) (Z : Set ((SmallEtale.toScheme B X.obj X.property).obj W))
    (hZ : IsLocallyClosed Z) (a : Λ) :
    (supportedSectionsSheafMap B X.obj X.property
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) (F ⊗ H) a).asHom W Z hZ).comp
        (tensorSupportedSectionsHom B Λ F H W h Z hZ) =
      (tensorSupportedSectionsHom B Λ F H W h Z hZ).comp
        (supportedSectionsSheafMap B X.obj X.property
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a).asHom W Z hZ) :=
  AddMonoidHom.ext fun s => Subtype.ext
    (((tensorSectionHom B Λ F H W h
      (supportOpen B X.obj X.property W Z hZ)).hom.map_smul a s.val).symm)

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The projection-formula recipe commutes with multiplication by a scalar.** -/
@[reassoc]
public theorem finiteSupportTensorSectionsHom_scalar
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (a : Λ) :
    finiteSupportTensorSectionsHom B Λ f F G V t ≫
        colim.map (finiteSupportDiagramMap B f
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property)
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) a).asHom V) =
      colim.map (finiteSupportDiagramMap B f
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a).asHom V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V t := by
  have hΘ :
      (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
            (baseChange B f V) (modPullbackUnitSection B Λ f G V t)).finiteSupportDiagramHom
          B f ≫
        finiteSupportDiagramMap B f
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property)
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) a).asHom V =
      finiteSupportDiagramMap B f
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a).asHom V ≫
        (tensorOpenSectionMap B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f V) (modPullbackUnitSection B Λ f G V t)).finiteSupportDiagramHom
            B f :=
    NatTrans.ext (funext fun E => AddCommGrpCat.hom_ext
      (tensorSupportedSectionsHom_comp_scalar B Λ F
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (baseChange B f V)
        (modPullbackUnitSection B Λ f G V t) E.1
        (finiteSupport_isLocallyClosed B f V E) a))
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hΘ]

/-- The projection-formula recipe, transported into the values of `f_{p!}`, commutes with the
scalar action on those values. This is the `Λ`-linearity of
`AlgebraicGeometry.SmallEtale.modFiniteSupportTensorHom`, stated in terms of the values of
`f_{p!}` themselves. -/
public theorem finiteSupportTensorSectionsHom_eqToHom_scalar
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (a : Λ) :
    (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).2.obj_eq
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
          finiteSupportTensorSectionsHom B Λ f F G V t ≫
          eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).2.obj_eq
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm) ≫
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.map
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property)
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) a).asHom).app (op V) =
      ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.map
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a).asHom).app (op V) ≫
        (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).2.obj_eq
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
          finiteSupportTensorSectionsHom B Λ f F G V t ≫
          eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).2.obj_eq
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm) := by
  rw [finiteSupportPushforward_map_app.{u, max (u + 1) v} B f (fun _ => inferInstance) _ V,
    finiteSupportPushforward_map_app.{u, max (u + 1) v} B f (fun _ => inferInstance) _ V]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    finiteSupportTensorSectionsHom_scalar_assoc]

/-- **The projection-formula recipe as a morphism of `Λ`-modules.** For a section `t` of `G`
over a test object `V`, the recipe `(Z, s) ↦ (Z, s ⊗ f^{-1}t)` of [Stacks, Tag 0GKF] is a
`Λ`-linear map `f_{p!}F(V) ⟶ f_{p!}(F ⊗_Λ f^{-1}G)(V)`. -/
public def modFiniteSupportTensorHom (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) :
    ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V) ⟶
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).obj (op V) :=
  ModuleCat.homMk
    (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
        finiteSupportTensorSectionsHom B Λ f F G V t ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm)
    (finiteSupportTensorSectionsHom_eqToHom_scalar B Λ f F G V t)

end Tensor

end AlgebraicGeometry.SmallEtale

end
