module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Internal Hom is invariant under an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `e : C ≌ D` be an equivalence of the
underlying sites, continuous in both directions, together with structure maps
`φ : O_C ⟶ e_* O_D` and `ψ : O_D ⟶ (e^{-1})_* O_C` exhibiting the two pushforwards of modules as
mutually inverse equivalences. Then the induced equivalence of categories of sheaves of modules
carries the internal Hom sheaf of Stacks 03EM to the internal Hom sheaf,

`φ_* Hom_{O_D}(A, B) ≅ Hom_{O_C}(φ_* A, φ_* B)`.

The proof is the one of Stacks 0E8H, with the iterated-slice equivalence `(C/U)/V ≌ C/V` there
replaced by the equivalence of slices `C/W ≌ D/e(W)` induced by `e`. Both sides have the same
sections over an object `W` of `C`: on the left they are the morphisms `A|_{e(W)} ⟶ B|_{e(W)}` on
`D/e(W)`, read as an `O_C(W)`-module along `φ`, and on the right the morphisms
`(φ_* A)|_W ⟶ (φ_* B)|_W` on `C/W`. The equivalence of slices carries one to the other, and the
comparison it induces is already a map of presheaves of modules, so it suffices to see that it
is bijective on each such set of sections.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.siteEquivPhiOver` and `siteEquivPsiOver`: the two structure
  maps, localized at an object `W` of `C`.
* `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`: the equivalence between sheaves of
  modules on `D/e(W)` and on `C/W`, induced by the equivalence of slices.
* `Stacks.SheafOfModules.InternalHom.siteEquivSection` and `siteEquivSectionEquiv`: the
  comparison on sections over `W`, and the proof that it is a bijection.
* `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomHom`: the comparison, as a morphism of
  presheaves of modules on `C`.
* `Stacks.SheafOfModules.InternalHom.psiOfIso`: when `φ` is invertible, the inverse structure map
  it determines, so that a consumer need supply only `φ`.

## Main results

* `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso`: **the transport**, the
  isomorphism `φ_* Hom_{O_D}(A, B) ≅ Hom_{O_C}(φ_* A, φ_* B)` of sheaves of modules.
* `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso_hom_app`: on sections it is
  restriction of a local morphism along the slice functor `C/W ⥤ D/e(W)`. This pins the
  isomorphism down, rather than merely asserting that some isomorphism exists.
* `Stacks.SheafOfModules.InternalHom.psiOfIso_counit` and
  `Stacks.SheafOfModules.InternalHom.psiOfIso_unit`: the two compatibilities for `psiOfIso`, the
  second of them the triangle identity of the equivalence of sites.
* `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso`: the transport, for an
  equivalence of sites together with an invertible structure map alone.

## Implementation notes

This is the statement of Stacks 0E8H for an equivalence of ringed sites rather than for
restriction to a localization, and it is not the tag:
`Stacks.SheafOfModules.InternalHom.internalHomOverIso` is, and neither statement is an instance of
the other — there the comparison is along the slice projection `C/U ⥤ C`, which is not an
equivalence, and here it is along an equivalence of sites, which need not be a localization.
Nothing below therefore carries a `@[stacks]` attribute.

The hypotheses are exactly the data of Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence`, so that a consumer who already has such an
equivalence — as `AlgebraicGeometry.Scheme.Modules.overEquiv` and
`Stacks.SheafOfModules.InternalHom.sliceModulesEquiv` both are — can feed it in directly. Only `φ`
enters the statement; `ψ` and the two compatibilities `H₁`, `H₂` are used
solely to know that the localized pushforward is fully faithful, which is what makes the
comparison on sections bijective. A consumer who has `φ` and knows it invertible — the usual
situation, since the two compatibilities force it — can use `siteEquivInternalHomIsoOfIso`
instead and let `psiOfIso` supply the rest. Its invertibility hypothesis is the *named*
instance argument `hφ`, so that it can be passed by hand when the two interchangeable `Category`
instances of `CategoryTheory.Sheaf` keep synthesis from finding it.

The equivalence of slices is Mathlib's `CategoryTheory.Over.postEquiv`. Its continuity is
`CategoryTheory.Functor.isContinuous_overPost` for the forward direction and that together with
continuity of `CategoryTheory.Over.map` for the backward one; Mathlib has only the cocontinuous
half as an instance, which is why the two instances below are supplied by hand.

The localized structure maps are `φ` and `ψ` whiskered along the slice projections, which is
possible because `Over.post e.functor ⋙ Over.forget (e(W))` and `Over.forget W ⋙ e.functor` are
the same functor. With that choice the identification of `(φ_* A)|_W` with the transport of
`A|_{e(W)}` is definitional, which is what keeps the comparison free of `eqToHom`.

Two steps are not definitional and are the only places where the hypotheses on `φ` are used.
That the comparison is `O_C(W)`-linear is the naturality of `φ` — over a slice object
`T ⟶ W`, restricting a section of `O_C` over `W` and then pushing it along `φ` agrees with
pushing it and then restricting. That the comparison is natural in `W` needs
`e.functor.map (T.hom ≫ f) = e.functor.map T.hom ≫ e.functor.map f`, which identifies the two
slice objects at which the local morphism is evaluated; the identification is transported
through `eq_of_heq`, the two sides of the resulting equation having definitionally equal types.

## References

* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

universe u v w m u' v'

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]

/-- The forward functor of the equivalence of slices `C/W ≌ D/e(W)` is continuous for the
localized topologies. -/
instance postEquivFunctorIsContinuous (W : C) :
    (Over.postEquiv (X := W) e).functor.IsContinuous (J.over W) (K.over (e.functor.obj W)) :=
  Functor.isContinuous_overPost J K e.functor W

/-- The backward functor of the equivalence of slices `C/W ≌ D/e(W)` is continuous for the
localized topologies: it is `Over.post e.inverse` followed by `Over.map` of the unit. -/
instance postEquivInverseIsContinuous (W : C) :
    (Over.postEquiv (X := W) e).inverse.IsContinuous (K.over (e.functor.obj W)) (J.over W) := by
  have h₁ : (Over.post (X := e.functor.obj W) e.inverse).IsContinuous (K.over (e.functor.obj W))
      (J.over (e.inverse.obj (e.functor.obj W))) :=
    Functor.isContinuous_overPost K J e.inverse _
  have h₂ : (Over.map (e.unitIso.inv.app W)).IsContinuous
      (J.over ((e.functor ⋙ e.inverse).obj W)) (J.over ((𝟭 C).obj W)) := inferInstance
  exact Functor.isContinuous_comp _ _ _ (J.over (e.inverse.obj (e.functor.obj W))) _

end CategoryTheory.Over

namespace Stacks.SheafOfModules.InternalHom

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The structure map `O_C ⟶ e_* O_D` of the equivalence, localized at an object `W` of `C`: it
is `φ` whiskered along the slice projection, which is possible because restricting along the
slice functor `C/W ⥤ D/e(W)` and then along `Over.forget` is restricting along
`Over.forget` and then along `e`. -/
def siteEquivPhiOver (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⟶
      (((Over.postEquiv (X := W) eqv).functor).sheafPushforwardContinuous RingCat.{w}
        (Y.J.over W) (X.J.over (eqv.functor.obj W))).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) :=
  ⟨Functor.whiskerLeft (Over.forget W).op φ.hom⟩

/-- The structure map `O_D ⟶ (e^{-1})_* O_C` of the equivalence, localized at `W`. -/
def siteEquivPsiOver (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ⟶
      (((Over.postEquiv (X := W) eqv).inverse).sheafPushforwardContinuous RingCat.{w}
        (X.J.over (eqv.functor.obj W)) (Y.J.over W)).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  ⟨Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op ψ.hom⟩

variable
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- Sheaves of modules on the localization `D/e(W)` and on the localization `C/W` agree, along
the equivalence of slices `C/W ≌ D/e(W)` induced by `e`. The two structure maps are `φ` and `ψ`
whiskered along the slice projections, and the two compatibilities they must satisfy are those
of `φ` and `ψ`, read at the underlying object of a slice object. -/
def siteEquivModulesOver (W : Y.C) :
    _root_.SheafOfModules.{m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ≌
      _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.postEquiv (X := W) eqv)
    (siteEquivPhiOver eqv φ W) (siteEquivPsiOver eqv ψ W)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₁)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₂)

variable (A B : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A morphism `A|_{e(W)} ⟶ B|_{e(W)}` on `D/e(W)`, read as a morphism
`(φ_* A)|_W ⟶ (φ_* B)|_W` on `C/W`. -/
def siteEquivSection (W : Y.C)
    (α : internalHomObj X.O.obj A.val B.val (eqv.functor.obj W)) :
    internalHomObj Y.O.obj ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val
      ((_root_.SheafOfModules.pushforward.{m} φ).obj B).val W := by
  let e := siteEquivModulesOver eqv φ ψ H₁ H₂ W
  let α₁ : _root_.SheafOfModules.over A (eqv.functor.obj W) ⟶
      _root_.SheafOfModules.over B (eqv.functor.obj W) :=
    (_root_.SheafOfModules.fullyFaithfulForget _).preimage α
  exact (_root_.SheafOfModules.forget _).map (e.functor.map α₁)

/-- The comparison on sections over `W` is a bijection: the equivalence of slices induces an
equivalence of the categories of sheaves of modules, which is fully faithful, and so is the
forgetful functor from sheaves of modules. -/
def siteEquivSectionEquiv (W : Y.C) :
    ((internalHomObj X.O.obj A.val B.val (eqv.functor.obj W)) : Type _) ≃
      ((internalHomObj Y.O.obj ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B).val W) : Type _) := by
  let e := siteEquivModulesOver eqv φ ψ H₁ H₂ W
  let hA := _root_.SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W))
  let hA' := _root_.SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)
  exact (hA.homEquiv (X := _root_.SheafOfModules.over A (eqv.functor.obj W))
      (Y := _root_.SheafOfModules.over B (eqv.functor.obj W))).symm.trans
    ((e.fullyFaithfulFunctor.homEquiv).trans (hA'.homEquiv))

/-- The comparison `φ_* Hom_{O_D}(A, B) ⟶ Hom_{O_C}(φ_* A, φ_* B)`, as a morphism of presheaves
of modules on `C`. -/
def siteEquivInternalHomHom :
    RingedSite.valOf Y ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)) ⟶
      RingedSite.valOf Y (RingedSite.internalHomSheaf Y
        ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)) where
  app W := by
    letI : Module ((Oforget Y.O.obj).obj W)
        (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
          (RingedSite.internalHomSheaf X A B)).val.obj W) :=
      (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)).val.obj W).isModule
    letI : AddCommGroup
        (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
          (RingedSite.internalHomSheaf X A B)).val.obj W) :=
      (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)).val.obj W).isAddCommGroup
    letI : Module ((Oforget Y.O.obj).obj W)
        ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
          ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W) :=
      ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W).isModule
    letI : AddCommGroup
        ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
          ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W) :=
      ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W).isAddCommGroup
    exact ConcreteCategory.ofHom (C := ModuleCat ((Oforget Y.O.obj).obj W))
      { toFun := fun α => siteEquivSection eqv φ ψ H₁ H₂ A B W.unop α
        map_add' := by
          intro α β; apply PresheafOfModules.hom_ext; intro T
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
        map_smul' := by
          intro r α; apply PresheafOfModules.hom_ext; intro T
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
          have key : (fRestr X.O.obj (eqv.functor.obj W.unop) ((φ.hom.app W).hom r)
              ((Over.post eqv.functor).op.obj T))
              = (φ.hom.app (op T.unop.left)).hom (fRestr Y.O.obj W.unop r T) := by
            have h := ConcreteCategory.congr_hom (φ.hom.naturality T.unop.hom.op) r
            simp only [RingCat.hom_comp, RingHom.coe_comp] at h
            exact h.symm
          change (fRestr X.O.obj (eqv.functor.obj W.unop)
              ((φ.hom.app W).hom r) ((Over.post eqv.functor).op.obj T)) •
                (ModuleCat.Hom.hom (α.app ((Over.post eqv.functor).op.obj T)) x) = _
          rw [key]
          rfl }
  naturality := by
    intro W Z f; apply ModuleCat.hom_ext; apply LinearMap.ext; intro α
    apply PresheafOfModules.hom_ext; intro T
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    have hO : (Over.map (eqv.functor.map f.unop)).obj
          ((Over.post eqv.functor).obj T.unop)
        = (Over.post eqv.functor).obj ((Over.map f.unop).obj T.unop) :=
      congrArg Over.mk (eqv.functor.map_comp T.unop.hom f.unop).symm
    have key : α.app (op ((Over.map (eqv.functor.map f.unop)).obj
          ((Over.post eqv.functor).obj T.unop)))
        = α.app (op ((Over.post eqv.functor).obj ((Over.map f.unop).obj T.unop))) := by
      have h : HEq (α.app (op ((Over.map (eqv.functor.map f.unop)).obj
            ((Over.post eqv.functor).obj T.unop))))
          (α.app (op ((Over.post eqv.functor).obj ((Over.map f.unop).obj T.unop)))) := by
        rw [hO]
      exact eq_of_heq h
    change (ModuleCat.Hom.hom (α.app (op ((Over.map (eqv.functor.map f.unop)).obj
        ((Over.post eqv.functor).obj T.unop))))) x = _
    rw [key]
    rfl

/-- **Internal Hom is invariant under an equivalence of ringed sites.** The equivalence of
categories of sheaves of modules induced by an equivalence of the underlying sites, together
with compatible structure maps, carries the internal Hom sheaf of Stacks 03EM to the internal
Hom sheaf. -/
def siteEquivInternalHomIso :
    (_root_.SheafOfModules.pushforward.{max u v m} φ).obj (RingedSite.internalHomSheaf X A B) ≅
      RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B) :=
  let app : ∀ W, ((RingedSite.valOf Y ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
      (RingedSite.internalHomSheaf X A B))).obj W) ≅
      ((RingedSite.valOf Y (RingedSite.internalHomSheaf Y
        ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B))).obj W) := fun W => by
    letI : IsIso ((siteEquivInternalHomHom eqv φ ψ H₁ H₂ A B).app W) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (siteEquivSection eqv φ ψ H₁ H₂ A B W.unop)
      exact (siteEquivSectionEquiv eqv φ ψ H₁ H₂ A B W.unop).bijective
    exact asIso ((siteEquivInternalHomHom eqv φ ψ H₁ H₂ A B).app W)
  (_root_.SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).preimageIso
    (PresheafOfModules.isoMk app (by
      intro W Z f
      exact (siteEquivInternalHomHom eqv φ ψ H₁ H₂ A B).naturality f))

/-- At an object `W` of `C`, the transport restricts a local morphism along the slice functor
`C/W ⥤ D/e(W)`. -/
theorem siteEquivInternalHomIso_hom_app (W : Y.Cᵒᵖ)
    (α : ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
      (RingedSite.internalHomSheaf X A B)).val.obj W)
    (T : (Over W.unop)ᵒᵖ)
    (x : ((restrFun Y.O.obj W.unop).obj
      ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val).obj T) :
    ((((siteEquivInternalHomIso eqv φ ψ H₁ H₂ A B).hom.val.app W).hom α).app T).hom x =
      (α.app ((Over.post eqv.functor).op.obj T)).hom x :=
  rfl

end Stacks.SheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [hφ : IsIso φ]

/-- An invertible structure map of sheaves of rings is invertible on underlying presheaves:
sheaves of rings are a full subcategory of presheaves of rings. -/
instance isIso_hom_of_isIso : IsIso φ.hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf Y.J RingCat.{w}).map φ))

/-- The inverse structure map determined by an invertible `φ`: transport along the counit of the
equivalence of sites, then invert `φ`. -/
def psiOfIso : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  ⟨Functor.whiskerRight (NatTrans.op eqv.counit) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ≫
    Functor.whiskerLeft eqv.inverse.op (inv φ.hom)⟩

/-- The first compatibility, for the inverse structure map built from an invertible `φ`: it
holds because `psiOfIso` was defined by cancelling `φ` off it. -/
theorem psiOfIso_counit :
    Functor.whiskerRight (NatTrans.op eqv.counit) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      (psiOfIso eqv φ).hom ≫ eqv.inverse.op.whiskerLeft φ.hom := by
  ext W x
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id φ.hom) (eqv.inverse.op.obj W))
    ((RingCat.Hom.hom ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map
      (eqv.counit.app W.unop).op)) x)).symm

/-- The second compatibility, for the inverse structure map built from an invertible `φ`. Since
`φ` is invertible it suffices to check the identity after composing with `φ` again, and then
naturality of `φ` turns the statement into the triangle identity
`e(η_W) ≫ ε_{e(W)} = 𝟙` of the equivalence of sites. -/
theorem psiOfIso_unit :
    φ.hom ≫ eqv.functor.op.whiskerLeft (psiOfIso eqv φ).hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
        𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj := by
  ext W : 2
  obtain ⟨W⟩ := W
  have hn := φ.hom.naturality (eqv.unit.app W).op
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj, Functor.op_map] at hn
  have hi : (inv φ.hom).app (op (eqv.inverse.obj (eqv.functor.obj W))) ≫
      φ.hom.app (op (eqv.inverse.obj (eqv.functor.obj W))) = 𝟙 _ :=
    (asIso φ.hom).inv_hom_id_app _
  simp only [psiOfIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app, Category.assoc]
  rw [← cancel_mono (φ.hom.app (op W))]
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj]
  simp only [Category.assoc, Category.id_comp]
  rw [hn, ← Category.assoc ((inv φ.hom).app _) (φ.hom.app _), hi, Category.id_comp]
  change φ.hom.app (op W) ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map
        (eqv.counit.app (eqv.functor.obj W)).op ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.functor.map (eqv.unit.app W)).op =
    φ.hom.app (op W)
  have ht : eqv.functor.map (eqv.unit.app W) ≫ eqv.counit.app (eqv.functor.obj W) = 𝟙 _ :=
    eqv.functor_unit_comp W
  rw [← Functor.map_comp, ← op_comp, ht]
  simp only [Functor.id_obj, Functor.op_obj, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id (φ.hom.app (op W))

/-- **Internal Hom is invariant under an equivalence of sites with an invertible structure
map.** This is `siteEquivInternalHomIso` with the inverse structure map and the two
compatibilities supplied by `psiOfIso`, so that only `φ` and its invertibility are needed. -/
def siteEquivInternalHomIsoOfIso
    (A B : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (_root_.SheafOfModules.pushforward.{max u v m} φ).obj (RingedSite.internalHomSheaf X A B) ≅
      RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B) :=
  siteEquivInternalHomIso eqv φ (psiOfIso eqv φ) (psiOfIso_counit eqv φ)
    (psiOfIso_unit eqv φ) A B

end Stacks.SheafOfModules.InternalHom

end
