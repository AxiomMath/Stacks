module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModulePullbackGerm

/-!
# The projection map on a generator of the finite-support stalk

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The sections of
`f_{p!}F` over a test object `V` are the colimit of the groups of sections supported on the
supports finite over `V`, and a section `a` supported on such a support `Z` gives a generator
`(Z, a)` of that colimit. This file computes the projection map of
`AlgebraicGeometry.SmallEtale.modFiniteSupportTensorPresheafMap` on such a generator: it is the
generator `(Z, a ⊗ f^{-1}t)` of the same support.

This is what puts the germ formula of
`AlgebraicGeometry.SmallEtale.toPresheafFiber_modFiniteSupportTensorPresheafMap` in contact with
the germ characterization `AlgebraicGeometry.SmallEtale.finiteSupportStalkToFiberStalks_germ` of
the decomposition `(f_{p!}F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`, both of which are stated on generators.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiniteSupportGenerator` — a section supported on a support
  finite over `V`, read as a section of `f_{p!}F` over `V`.

## Main results

* `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorHom_generator` — **the projection map on a
  generator**: `(Z, a) ↦ (Z, a ⊗ f^{-1}t)`.
* `AlgebraicGeometry.SmallEtale.presheafFiberModFiniteSupportStalkIso` — **the stalk of
  `f_{p!}F` decomposes over the geometric fibre, `Λ`-linearly**, on the fibre formed on
  presheaves, which is the one the projection map's stalk is computed with.
* `AlgebraicGeometry.SmallEtale.modFiniteSupportGenerator_comp_presheafFiber` — **the germ of a
  generator decomposes into the germs of the supported section**: the germ of `(Z, a)`, read
  through the comparison of the `Λ`-module fibre with the abelian fibre and then through the
  decomposition of Stacks 0F6P, is the family of germs of `a` over the geometric fibre.

## Implementation notes

The values of `AlgebraicGeometry.SmallEtale.modFiniteSupportPresheaf` are the colimits of
supported sections only up to the propositional equality
`AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec.obj_eq`, so the generator is the
colimit inclusion followed by that transport. The cancellation of the transport against its
inverse is isolated in `Stacks.comp_eq_comp_of_cancel`, an identity between abstract morphisms,
because the concrete composites are not type-correct at the `implicit` transparency level at
which `rw` checks its motives — the same reason the other steps of this computation use abstract
re-association helpers.

Nothing here carries a `stacks` attribute: this is one step of the stalk computation behind
[Stacks, Tag 0GKF] and not that tag.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace Stacks

/-- Rewriting a middle pair of factors by an identity, under a leading factor. Isolated as a
statement about abstract morphisms so that it applies to terms whose types agree only up to
unfolding a definition. -/
public theorem comp_comp_of_eq {C : Type*} [Category* C] {A P Q R S : C} (g : A ⟶ P)
    (a : P ⟶ Q) (i : Q ⟶ R) (k : R ⟶ S) (tb : P ⟶ R) {r : A ⟶ S}
    (h1 : a ≫ i = tb) (h2 : g ≫ tb ≫ k = r) : g ≫ a ≫ i ≫ k = r := by
  rw [← Category.assoc a i k, h1, h2]

/-- **A middle transport cancels, and a generator formula transfers.** If `e' ≫ e` is the
identity and `i ≫ T = b ≫ j`, then the transported composite is computed by `b` and `j`.
Isolated as a statement about abstract morphisms so that it applies to terms whose types agree
only up to unfolding a definition. -/
public theorem comp_eq_comp_of_cancel {C : Type*} [Category* C] {A A' P W Q R : C}
    (i : A ⟶ P) (e' : P ⟶ W) (e : W ⟶ P) (T : P ⟶ Q) (k : Q ⟶ R) (b : A ⟶ A') (j : A' ⟶ Q)
    (he : e' ≫ e = 𝟙 P) (h1 : i ≫ T = b ≫ j) :
    (i ≫ e') ≫ e ≫ T ≫ k = b ≫ j ≫ k := by
  rw [Category.assoc, ← Category.assoc e' e, he, Category.id_comp, ← Category.assoc, h1,
    Category.assoc]

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **A supported section, read as a section of `f_{p!}F` over the test object.** The colimit
inclusion at the support, followed by the identification of the values of `f_{p!}` with the
colimits of supported sections. -/
public def modFiniteSupportGenerator (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).obj E ⟶
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).obj
        (((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)) :=
  colimit.ι (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V)
      E ≫
    eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).symm

/-- **The projection map on a generator.** A section `a` supported on a support `Z` finite over
the test object `V`, tensored with a section `t` of `G` over `V`, is the generator of the same
support `Z` carrying `a ⊗ f^{-1}t`. -/
public theorem modFiniteSupportTensorHom_generator
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (t : G.obj.obj (op V)) (E : FiniteSupport B f V) :
    modFiniteSupportGenerator B Λ f F V E ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (modFiniteSupportTensorHom B Λ f F G V t) =
      AddCommGrpCat.ofHom (tensorSupportedSectionsHom B Λ F
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f V) (modPullbackUnitSection B Λ f G V t) E.1
          (finiteSupport_isLocallyClosed B f V E)) ≫
        modFiniteSupportGenerator B Λ f (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))
          V E := by
  let h := (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq
    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V
  exact Stacks.comp_eq_comp_of_cancel _ (eqToHom h.symm) (eqToHom h) _
    (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V).symm) _ _
    (by rw [eqToHom_trans, eqToHom_refl]) (finiteSupportTensorSectionsHom_ι B Λ f F G V t E)

/-- **The stalk of `f_{p!}F` decomposes over the geometric fibre, `Λ`-linearly.** The fibre of
`f_{p!}F` at a geometric point `ȳ` of `Y`, formed on presheaves, is the direct sum of the stalks
of `F` over the points of the geometric fibre: the stalk of a presheaf is the stalk of its
sheafification, that sheafification is `f_!F` by
`AlgebraicGeometry.SmallEtale.fShriekModSheafifyIso`, and its stalk decomposes by
`AlgebraicGeometry.SmallEtale.modShriekStalkIso`, the `Λ`-linear form of Stacks 0F5F. -/
public def presheafFiberModFiniteSupportStalkIso
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (s : GeometricPoint Y.obj) :
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≅
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F := by
  letI : HasProducts.{u} (ModuleCat.{max (u + 1) v} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  exact (((geometricPointSitePoint B Y.obj Y.property s).presheafToSheafCompSheafFiberIso
      (ModuleCat.{max (u + 1) v} Λ)).app
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)).symm ≪≫
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).mapIso
      (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).symm ≪≫
    (modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F

/-- **The germ of a generator decomposes into the germs of the supported section.** The germ at
a pointed étale neighbourhood `U` of `ȳ` of the generator `(Z, a)` of `f_{p!}F`, read through the
comparison of the `Λ`-module fibre with the abelian fibre and then through the decomposition
`(f_{p!}F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄` of Stacks 0F6P, is the family of germs of `a` at the points of
the geometric fibre.

This is the germ formula the stalk computation of [Stacks, Tag 0GKF] needs on both sides of the
projection map. It is `AlgebraicGeometry.SmallEtale.finiteSupportStalkToFiberStalks_generator`
together with Mathlib's germ formula for the commutation of a fibre with a functor preserving
filtered colimits. -/
public theorem modFiniteSupportGenerator_comp_presheafFiber
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (s : GeometricPoint Y.obj)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1) :
    modFiniteSupportGenerator B Λ f F U.1 E ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≫
          (((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
              (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).app
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)).inv ≫
            finiteSupportStalkToFiberStalks.{u, max (u + 1) v} B f s
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) (fun _ => inferInstance) =
      fiberStalkHom.{u, max (u + 1) v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) U.1 U.2 E := by
  have hgerm :=
    (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber_presheafFiberCompIso_hom_app
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) U.1 U.2
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)
  have h1 : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≫
      (((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)).inv =
      (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)) :=
    (Iso.comp_inv_eq _).2 hgerm.symm
  exact Stacks.comp_comp_of_eq _ _ _ _ _ h1
    ((Category.assoc _ _ _).trans
      (finiteSupportStalkToFiberStalks_generator.{u, max (u + 1) v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) (fun _ => inferInstance) U E))

end AlgebraicGeometry.SmallEtale

end
