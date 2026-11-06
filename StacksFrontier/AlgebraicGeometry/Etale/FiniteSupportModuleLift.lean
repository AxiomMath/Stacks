module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresheafEndActionLift
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift

/-!
# The finite-support direct image with coefficients in a ring

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `Λ` be a ring.
The finite-support direct image `f_{p!}` of Stacks 0F6M is a functor from abelian sheaves on
`X_étale` to abelian *presheaves* on `Y_étale`. This file lifts it to a functor from sheaves of
`Λ`-modules to presheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportPushforward_additive` — **`f_{p!}` is additive.**
  Its action on a morphism of abelian sheaves is pinned down on the colimit generators by
  `AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec.map_sheaf`, and there it is the
  action of that morphism on supported sections, which is additive.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiniteSupportPresheaf` — **the finite-support direct image
  of sheaves of `Λ`-modules**, `Stacks.ModuleCatLift.presheafLift` applied to `f_{p!}`.

## Implementation notes

Additivity is the hypothesis every lift to `Λ`-modules of the file
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift` needs, and it is the only thing
missing for `f_{p!}`: `AlgebraicGeometry.SmallEtale.fShriekMod` exists because
`AlgebraicGeometry.SmallEtale.fShriekFunctor` is additive by Stacks 0F5F, but that is the
*sheafified* functor.

`AlgebraicGeometry.SmallEtale.finiteSupportPushforward` is given as a subtype: a functor
together with `AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec`, which characterizes
it on the colimit generators only after transporting along the equality of its values with the
colimits. So the proof below conjugates by those `eqToHom`s and then uses that the colimit
generators are jointly epimorphic.

Nothing here carries a `stacks` attribute: the functor is the one of Stacks 0F6M, already
attributed to `AlgebraicGeometry.SmallEtale.finiteSupportPushforward`, and the only thing added
is the `Λ`-action, which is formal.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v r

section SupportedSectionsAdd

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}}

/-- The action of a morphism of abelian sheaves on sections supported on a locally closed
subset is additive in that morphism. -/
public theorem supportedSectionsSheafMap_add (φ ψ : F ⟶ G) (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z) :
    supportedSectionsSheafMap B S hS (φ + ψ) W Z hZ =
      supportedSectionsSheafMap B S hS φ W Z hZ +
        supportedSectionsSheafMap B S hS ψ W Z hZ :=
  AddMonoidHom.ext fun _ => Subtype.ext rfl

end SupportedSectionsAdd

section Additive

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V))

/-- **The finite-support direct image is additive.** -/
public theorem finiteSupportPushforward_additive :
    (finiteSupportPushforward.{u, v} B f hsmall).1.Additive := by
  refine ⟨fun {F G φ ψ} => NatTrans.ext (funext fun V => ?_)⟩
  have spec := (finiteSupportPushforward.{u, v} B f hsmall).2
  let := hsmall V.unop
  have key :
      eqToHom (spec.obj_eq F V.unop).symm ≫
          ((finiteSupportPushforward.{u, v} B f hsmall).1.map (φ + ψ)).app (op V.unop) ≫
            eqToHom (spec.obj_eq G V.unop) =
        eqToHom (spec.obj_eq F V.unop).symm ≫
          (((finiteSupportPushforward.{u, v} B f hsmall).1.map φ).app (op V.unop) +
            ((finiteSupportPushforward.{u, v} B f hsmall).1.map ψ).app (op V.unop)) ≫
            eqToHom (spec.obj_eq G V.unop) := by
    refine colimit.hom_ext fun E => ?_
    rw [spec.map_sheaf (φ + ψ) V.unop E, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.comp_add, spec.map_sheaf φ V.unop E, spec.map_sheaf ψ V.unop E]
    have hadd :
        AddCommGrpCat.ofHom (supportedSectionsSheafMap B X.obj X.property (φ + ψ)
            (baseChange B f V.unop) E.1 (finiteSupport_isLocallyClosed B f V.unop E)) =
          AddCommGrpCat.ofHom (supportedSectionsSheafMap B X.obj X.property φ
              (baseChange B f V.unop) E.1 (finiteSupport_isLocallyClosed B f V.unop E)) +
            AddCommGrpCat.ofHom (supportedSectionsSheafMap B X.obj X.property ψ
              (baseChange B f V.unop) E.1 (finiteSupport_isLocallyClosed B f V.unop E)) := by
      rw [supportedSectionsSheafMap_add B X.obj X.property φ ψ (baseChange B f V.unop) E.1
        (finiteSupport_isLocallyClosed B f V.unop E)]
      rfl
    exact (congrArg (fun m => m ≫ colimit.ι (finiteSupportDiagram B f G V.unop) E) hadd).trans
      (Preadditive.add_comp _ _ _ _ _ _)
  have h1 := (cancel_epi (eqToHom (spec.obj_eq F V.unop).symm)).1 key
  exact (cancel_mono (eqToHom (spec.obj_eq G V.unop))).1 h1

end Additive

section ModuleLift

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The finite-support direct image of sheaves of `Λ`-modules.** The `Λ`-linear lift of the
`f_{p!}` of Stacks 0F6M: a functor from sheaves of `Λ`-modules on `X_étale` to presheaves of
`Λ`-modules on `Y_étale` whose underlying abelian presheaf is the one `f_{p!}` produces. -/
public def modFiniteSupportPresheaf :
    ModuleSheaf.{u, v, r} B X Λ ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v r} Λ) :=
  letI := finiteSupportPushforward_additive.{u, max (u + 1) v r} B f (fun _ => inferInstance)
  Stacks.ModuleCatLift.presheafLift.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B X.obj X.property)
    (finiteSupportPushforward.{u, max (u + 1) v r} B f (fun _ => inferInstance)).1

/-- **The `Λ`-linear finite-support direct image lifts `f_{p!}`.** Forgetting the `Λ`-module
structure gives the `f_{p!}` of Stacks 0F6M on the underlying abelian sheaf, on the nose. -/
public theorem modFiniteSupportPresheaf_obj_comp_forget₂ (F : ModuleSheaf.{u, v, r} B X Λ) :
    (modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F ⋙
        forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r} =
      (finiteSupportPushforward.{u, max (u + 1) v r} B f (fun _ => inferInstance)).1.obj
        ((forgetModuleSheaf.{u, v, r} B X Λ).obj F) :=
  rfl

/-- The scalar action on the sections of the `Λ`-linear finite-support direct image is the
image under `f_{p!}` of multiplication by that scalar. -/
public theorem modFiniteSupportPresheaf_obj_smul (F : ModuleSheaf.{u, v, r} B X Λ)
    (V : (SmallEtale B Y.obj Y.property)ᵒᵖ) (a : Λ) :
    (((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F).obj V).smul a =
      End.of (((finiteSupportPushforward.{u, max (u + 1) v r} B f (fun _ => inferInstance)).1.map
        (Stacks.ModuleCatLift.sheafScalarEnd Λ
          (SmallEtale.topology B X.obj X.property) F a).asHom).app V) :=
  rfl

end ModuleLift

end AlgebraicGeometry.SmallEtale

end
