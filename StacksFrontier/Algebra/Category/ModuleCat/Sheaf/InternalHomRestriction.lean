module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom commutes with restriction to a localized site

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `F`, `G` be sheaves of
`O`-modules. Restricting the internal Hom sheaf `Hom_O(F, G)` of Stacks 03EM to the localized
site `C/U` gives the internal Hom of the restrictions,

`Hom_O(F, G)|_U ≅ Hom_{O|_U}(F|_U, G|_U)`.

The proof is the one of the source. Both sides have the same sections over an object `V ⟶ U`
of `C/U`: on the left they are the morphisms `F|_V ⟶ G|_V` on `C/V`, and on the right the
morphisms `(F|_U)|_V ⟶ (G|_U)|_V` on the iterated slice `(C/U)/V`. The iterated-slice
equivalence `(C/U)/V ≌ C/V` carries one to the other, and the comparison it induces is already
a map of presheaves of modules, so it suffices to see that it is bijective on each such set of
sections.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`: the equivalence between sheaves of
  modules on `C/V` and on the iterated slice `(C/U)/V`, induced by the iterated-slice
  equivalence of sites.
* `Stacks.SheafOfModules.InternalHom.internalHomOverSection` and
  `internalHomOverSectionEquiv`: the comparison on sections over `V ⟶ U`, and the proof that
  it is a bijection.
* `Stacks.SheafOfModules.InternalHom.internalHomOverIsoHom`: the comparison, as a morphism of
  presheaves of modules on `C/U`.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomOverIso`: the isomorphism
  `Hom_O(F, G)|_U ≅ Hom_{O|_U}(F|_U, G|_U)`.
* `Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app`: on sections it is
  restriction of a local morphism along the iterated-slice functor. This pins the isomorphism
  down, rather than merely asserting that some isomorphism exists.

## Implementation notes

The internal Hom is Tag 03EM's presheaf `internalHom`, whose underlying presheaf that tag
shows to be a sheaf; an isomorphism of these presheaves of modules is therefore also the
asserted isomorphism of sheaves of modules. Restriction is Tag 03EM's `restrFun`, which on
sheaves of modules is `SheafOfModules.over`.

The equivalence of sheaves of modules along the iterated-slice equivalence of sites is built
from `SheafOfModules.pushforwardPushforwardEquivalence`, whose two structure maps are
identities here: the localized ring sheaf on `(C/U)/V` and the one on `C/V` have the same
underlying presheaf, both being `O` reindexed along the composite to `C`.

Everything here is stated at a module universe `m` independent of the universes of the ringed
site.  That matters for consumers on a site whose objects are larger than its coefficient
rings — the small étale site of an algebraic space over `Scheme.{u}` has its objects in
`Type (u + 1)` and its structure sheaf in `CommRingCat.{u}` — because there the internal Hom of
two modules in module universe `m` lands in `max (u + 1) m` rather than in `m`, so a statement
binding the module universe to that of the coefficient rings cannot be iterated.

## References

* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u v w m

/-- Sheaves of modules on the localized site `C/V` and on the iterated slice `(C/U)/V` agree,
along the iterated-slice equivalence `(C/U)/V ≌ C/V`. -/
noncomputable def sliceModulesEquiv (X : RingedSite.{u, v, w})
    (U : X.C) (V : Over U) :
    SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left) ≌
      SheafOfModules (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over V) := by
  let E := Over.iteratedSliceEquiv V
  let S := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over V
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left
  let φ : S ⟶ (E.functor.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (E.inverse.sheafPushforwardContinuous RingCat _ _).obj S := 𝟙 _
  exact _root_.SheafOfModules.pushforwardPushforwardEquivalence E φ ψ
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf X.O).1.map_id _)
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf X.O).1.map_id _)

/-- A morphism `F|_V ⟶ G|_V` on `C/V`, read as a morphism `(F|_U)|_V ⟶ (G|_U)|_V` on the
iterated slice `(C/U)/V`. -/
noncomputable def internalHomOverSection
    (X : RingedSite.{u, v, w}) (U : X.C) (V : Over U)
    (F G : _root_.SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (α : internalHomObj X.O.obj F.val G.val V.left) :
    internalHomObj ((X.O.over U).obj)
      ((restrFun X.O.obj U).obj F.val)
      ((restrFun X.O.obj U).obj G.val) V := by
  let e := sliceModulesEquiv X U V
  let α₁ : F.over V.left ⟶ G.over V.left :=
    (_root_.SheafOfModules.fullyFaithfulForget _).preimage α
  exact (_root_.SheafOfModules.forget _).map (e.functor.map α₁)

/-- The comparison on sections over `V ⟶ U` is a bijection: the iterated-slice equivalence is
fully faithful, and so is the forgetful functor from sheaves of modules. -/
noncomputable def internalHomOverSectionEquiv
    (X : RingedSite.{u, v, w}) (U : X.C) (V : Over U)
    (F G : _root_.SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((internalHomObj X.O.obj F.val G.val V.left) : Type _) ≃
      ((internalHomObj ((X.O.over U).obj)
        ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val) V) : Type _) := by
  let e := sliceModulesEquiv X U V
  let A := F.over V.left
  let B := G.over V.left
  let A' := (F.over U).over V
  let B' := (G.over U).over V
  let hA := _root_.SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left)
  let hA' := _root_.SheafOfModules.fullyFaithfulForget
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over V)
  exact (hA.homEquiv (X := A) (Y := B)).symm.trans
    ((e.fullyFaithfulFunctor.homEquiv (X := A) (Y := B)).trans
      (hA'.homEquiv (X := A') (Y := B')))

/-- The comparison of Stacks 0E8H as a morphism of presheaves of modules on `C/U`. -/
noncomputable def internalHomOverIsoHom
    (X : RingedSite.{u, v, w}) (U : X.C)
    (F G : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val) ⟶
      internalHom (X.O.over U).obj
        ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val) where
  app V := by
    letI : Module ((ORestr X.O.obj U).obj V)
        (((restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val)).obj V) :=
      (((restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val)).obj V).isModule
    letI : Module ((ORestr X.O.obj U).obj V)
        ((internalHom (X.O.over U).obj
          ((restrFun X.O.obj U).obj F.val)
          ((restrFun X.O.obj U).obj G.val)).obj V) :=
      ((internalHom (X.O.over U).obj
        ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val)).obj V).isModule
    letI : AddCommGroup
        (((restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val)).obj V) :=
      (((restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val)).obj V).isAddCommGroup
    letI : AddCommGroup
        ((internalHom (X.O.over U).obj
          ((restrFun X.O.obj U).obj F.val)
          ((restrFun X.O.obj U).obj G.val)).obj V) :=
      ((internalHom (X.O.over U).obj
        ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val)).obj V).isAddCommGroup
    exact ConcreteCategory.ofHom (C := ModuleCat ((ORestr X.O.obj U).obj V))
      { toFun := fun α => internalHomOverSection X U V.unop F G α
        map_add' := by
          intro α β; apply PresheafOfModules.hom_ext; intro W
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
        map_smul' := by
          intro r α; apply PresheafOfModules.hom_ext; intro W
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl }
  naturality := by
    intro V Z f; apply ModuleCat.hom_ext; apply LinearMap.ext; intro α
    apply PresheafOfModules.hom_ext; intro W
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl

/-- **Stacks 0E8H.** Internal Hom commutes with restriction to the localized site over `U`. -/
@[stacks 0E8H]
noncomputable def internalHomOverIso
    (X : RingedSite.{u, v, w}) (U : X.C)
    (F G : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val) ≅
      internalHom (X.O.over U).obj
        ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val) :=
  let app : ∀ V, (((restrFun X.O.obj U).obj
      (internalHom X.O.obj F.val G.val)).obj V) ≅
      ((internalHom (X.O.over U).obj ((restrFun X.O.obj U).obj F.val)
        ((restrFun X.O.obj U).obj G.val)).obj V) := fun V => by
    letI : IsIso ((internalHomOverIsoHom X U F G).app V) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (internalHomOverSection X U V.unop F G)
      have he : (internalHomOverSectionEquiv X U V.unop F G).toFun =
          internalHomOverSection X U V.unop F G := by
        funext α
        let α₁ : F.over V.unop.left ⟶ G.over V.unop.left :=
          (_root_.SheafOfModules.fullyFaithfulForget _).preimage α
        change ((_root_.SheafOfModules.forget
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over V.unop)).map
            ((sliceModulesEquiv X U V.unop).functor.map α₁)) = _
        rfl
      rw [← he]
      exact (internalHomOverSectionEquiv X U V.unop F G).bijective
    exact asIso ((internalHomOverIsoHom X U F G).app V)
  PresheafOfModules.isoMk app (by
    intro V Z f
    simpa [app] using (internalHomOverIsoHom X U F G).naturality f)

/-- At `V ⟶ U`, the isomorphism of Stacks 0E8H restricts a local morphism along the
iterated-slice functor `(C/U)/V ⥤ C/V`. -/
@[stacks 0E8H "canonical component on sections"]
theorem internalHomOverIso_hom_app
    (X : RingedSite.{u, v, w}) (U : X.C)
    (F G : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : (Over U)ᵒᵖ)
    (α : ((restrFun X.O.obj U).obj (internalHom X.O.obj F.val G.val)).obj V)
    (W : (Over V.unop)ᵒᵖ)
    (x : ((restrFun (X.O.over U).obj V.unop).obj
      ((restrFun X.O.obj U).obj F.val)).obj W) :
    ((((internalHomOverIso X U F G).hom.app V).hom α).app W).hom x =
      (α.app ((Over.iteratedSliceForward V.unop).op.obj W)).hom x :=
  rfl

end Stacks.SheafOfModules.InternalHom

end
